import ControlStack.Core.Gate
import ControlStack.Scenarios.SC26Transaction
import ControlStack.TrustedBroker

/-! The finite deployment projection contains raw service identities and authority
edges, not a CompleteMediation premise. Unknown edges prevent acceptance. The
runtime link is explicitly residual. SC26 is used as a reusable exact-payload,
one-use and shared-budget contract (not a verified Python implementation).
Its arrival-after-HALT semantics are conservative for already published effects.
-/
namespace ControlStack.Deployment
open ControlStack

structure Node where
  id : Nat
  uid : Nat
  agent : Bool
  privileged : Bool
  hostNetwork : Bool
  /-- 0 agent, 1 broker, 2 receiver, 3 reviewer, 4 approver, 5 unsupported. -/
  role : Nat
  runtimeMatch : Bool
  deriving DecidableEq, Repr

structure Edge where
  source : Nat
  target : Nat
  /-- sink-write/credential/escape and database-access edges all count -/
  authority : Bool
  unknown : Bool
  write : Bool
  deriving DecidableEq, Repr

structure IR where
  nodes : List Node
  edges : List Edge
  receiver : Nat
  broker : Nat
  sink : Nat
  database : Nat
  deriving DecidableEq, Repr

/-- These checks use identity and edges, never authorization labels. -/
def BaseAccepted (d : IR) : Prop :=
  (∀ e ∈ d.edges, e.unknown = false) ∧
  (∀ e ∈ d.edges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧
  (∀ e ∈ d.edges, e.authority = true → e.target = d.database → e.source = d.receiver ∨ e.source = d.broker) ∧
  (∀ n ∈ d.nodes, n.privileged = false ∧ n.hostNetwork = false) ∧
  (∀ r ∈ d.nodes, r.id = d.receiver → ∀ a ∈ d.nodes, a.agent = true → a.uid ≠ r.uid) ∧
  (∃ e ∈ d.edges, e.source = d.receiver ∧ e.target = d.sink ∧ e.authority = true) ∧
  (∀ n ∈ d.nodes, 0 < n.uid)

instance (d : IR) : Decidable (BaseAccepted d) := by unfold BaseAccepted; infer_instance

/-- Finite closure includes the start and every edge except trusted mediation.
The explicit closure obligation below makes the bound independently checkable. -/
def reachable (d : IR) (start : Nat) : List Nat :=
  (List.range (d.nodes.length + d.edges.length + 4)).foldl (fun seen _ =>
    (seen ++ d.edges.filterMap (fun e =>
      if e.source ∈ seen ∧ e.target ≠ d.broker ∧ e.target ≠ d.receiver
      then some e.target else none)).eraseDups) [start]

def RoleChecked (d : IR) : Prop :=
  d.nodes.length = 6 ∧
  (d.nodes.filter (fun n => n.role == 0)).length = 2 ∧
  (d.nodes.filter (fun n => n.role == 1)).length = 1 ∧
  (d.nodes.filter (fun n => n.role == 2)).length = 1 ∧
  (d.nodes.filter (fun n => n.role == 3)).length = 1 ∧
  (d.nodes.filter (fun n => n.role == 4)).length = 1 ∧
  (∀ n ∈ d.nodes, (n.agent = true ↔ n.role = 0) ∧
    (n.id = d.broker ↔ n.role = 1) ∧ (n.id = d.receiver ↔ n.role = 2))

def IdentityChecked (d : IR) : Prop :=
  ∀ a ∈ d.nodes, ∀ b ∈ d.nodes, a.id ≠ b.id →
    (a.uid = b.uid ↔ ((a.id = d.broker ∧ b.id = d.receiver) ∨
                     (a.id = d.receiver ∧ b.id = d.broker)))

def WritersChecked (d : IR) : Prop :=
  (∀ e ∈ d.edges, e.target = d.sink → e.source = d.receiver ∧ e.write = true) ∧
  (∀ e ∈ d.edges, e.target = d.database → e.source = d.broker ∨ e.source = d.receiver) ∧
  ((d.edges.filter (fun e => e.target == d.sink && e.write)).map Edge.source = [d.receiver]) ∧
  (d.edges.filter (fun e => e.target == d.database && e.write)).length = 2 ∧
  (∃ e ∈ d.edges, e.target = d.database ∧ e.write = true ∧ e.source = d.broker) ∧
  (∃ e ∈ d.edges, e.target = d.database ∧ e.write = true ∧ e.source = d.receiver)

def NoBypass (d : IR) : Prop :=
  ∀ a ∈ d.nodes, a.agent = true →
    a.id ∈ reachable d a.id ∧ d.sink ∉ reachable d a.id ∧ d.database ∉ reachable d a.id ∧
    (∀ e ∈ d.edges, e.source ∈ reachable d a.id →
      e.target ≠ d.broker → e.target ≠ d.receiver → e.target ∈ reachable d a.id)

instance (d : IR) : Decidable (RoleChecked d) := by unfold RoleChecked; infer_instance
instance (d : IR) : Decidable (IdentityChecked d) := by unfold IdentityChecked; infer_instance
instance (d : IR) : Decidable (WritersChecked d) := by unfold WritersChecked; infer_instance
instance (d : IR) : Decidable (NoBypass d) := by unfold NoBypass; infer_instance

/-- The kernel checks the same finite configuration obligations as Python.
Runtime flags are input observations, not independent attestation. -/
structure Accepted (d : IR) : Prop where
  basic : BaseAccepted d
  roles : RoleChecked d
  identities : IdentityChecked d
  runtime : ∀ n ∈ d.nodes, n.runtimeMatch = true
  writers : WritersChecked d
  bypass : NoBypass d

instance (d : IR) : Decidable (Accepted d) :=
  decidable_of_iff (BaseAccepted d ∧ RoleChecked d ∧ IdentityChecked d ∧
    (∀ n ∈ d.nodes, n.runtimeMatch = true) ∧ WritersChecked d ∧ NoBypass d)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
     fun h => ⟨h.basic, h.roles, h.identities, h.runtime, h.writers, h.bypass⟩⟩

/-- Exclusive sink writer is DERIVED from the finite checked edge facts. -/
theorem exclusive_sink (d : IR) (h : Accepted d) (e : Edge)
    (member : e ∈ d.edges) (authority : e.authority = true) (sink : e.target = d.sink) :
    e.source = d.receiver := h.basic.2.1 e member authority sink

theorem database_custody (d : IR) (h : Accepted d) (e : Edge)
    (member : e ∈ d.edges) (authority : e.authority = true) (db : e.target = d.database) :
    e.source = d.receiver ∨ e.source = d.broker := h.basic.2.2.1 e member authority db

/-- Concrete runtime observations must be faithfully included in the IR;
this is the residual implementation/environment premise, not kernel-proved. -/
structure Faithful (d : IR) (actual : List Edge) : Prop where
  captured : ∀ e ∈ actual, e ∈ d.edges

/-- Every actual scoped sink writer is the receiver IF extraction is faithful. -/
theorem runtime_exclusive (d : IR) (actual : List Edge) (h : Accepted d)
    (faithful : Faithful d actual) (e : Edge) (member : e ∈ actual)
    (authority : e.authority = true) (sink : e.target = d.sink) : e.source = d.receiver :=
  exclusive_sink d h e (faithful.captured e member) authority sink

/-- From checked IR UID facts, an agent cannot carry the receiver identity. -/
theorem agent_not_receiver_uid (d : IR) (h : Accepted d) (r a : Node)
    (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes)
    (agent : a.agent = true) : a.uid ≠ r.uid := h.basic.2.2.2.2.1 r hr rid a ha agent

/-- Role IDs are supplied as model parameters; actual SO_PEERCRED and human
role bindings are part of the residual faithful abstraction. -/
def roles (d : IR) (receiverUID : Nat) (approvers admins : List Nat) : SC26.Roles :=
  ⟨(d.nodes.filter (fun n => n.agent)).map Node.uid, approvers, admins, receiverUID⟩

theorem agent_call_legal (d : IR) (h : Accepted d) (r a : Node)
    (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes)
    (agent : a.agent = true) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) :
    SC26.legal (roles d r.uid approvers admins) (.bankCall a.uid k tx) :=
  agent_not_receiver_uid d h r a hr rid ha agent

/-- Reuse exact approval, receiver idempotency and shared budget safety. Legal
operations are typed; the UID contract above discharges direct agent calls. -/
theorem protocol_safe (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)
    (hops : ∀ o ∈ ops, SC26.legal R o) : SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops) :=
  SC26.sc26_safe R cap ops hops

theorem one_use (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) :
    (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup := SC26.sc26_once R cap ops

/-- Reuse the gate invariant/log-prefix theorem rather than a new induction. -/
theorem gate_contract (R : SC26.Roles) (cap : Nat)
    (ops : List {o : SC26.Op // SC26.legal R o}) :
    (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧
    (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧
    ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops),
      (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e :=
  (SC26.spec R cap).trace_safe SC26.init ops (SC26.inv_init R cap)

/-- The actual broker model separately supplies joint budget/nonce invariants. -/
theorem broker_contract (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State)
    (trace : TrustedBroker.Trace R (TrustedBroker.initial cap) t) : TrustedBroker.Safe t :=
  TrustedBroker.trace_preserves R _ t (TrustedBroker.initial_safe cap) trace

/-- Faithful extraction exhausts effective runtime authority and identity facts.
This environmental inclusion remains unproved by source hashes or examples. -/
structure ExtractionFaithful (d : IR) (r : Node) (actualEdges : List Edge) : Prop where
  authority : Faithful d actualEdges
  receiverNode : r ∈ d.nodes
  receiverID : r.id = d.receiver

/-- Full protocol refinement, separately assumed from authority extraction.
publication is equality of actual sink effects and abstract model publication. -/
structure ProtocolRefinement (d : IR) (r : Node) (R : SC26.Roles) (cap : Nat)
    (ops : List SC26.Op) (sinkEffects : List (Nat × SC26.Tx)) : Prop where
  gateUID : R.gate = r.uid
  callerBinding : ∀ c k tx, SC26.Op.bankCall c k tx ∈ ops →
    ∃ a ∈ d.nodes, a.agent = true ∧ c = a.uid
  unitCosts : ∀ e ∈ sinkEffects, e.2.amount = 1
  publication : sinkEffects = (SC26.run R cap SC26.full SC26.init ops).bank

/-- Conditional deployment assurance: graph exclusivity and protocol safety
are joined through a substantive faithfulness premise, never CompleteMediation.
The caller-binding field plus IR UID facts derives the legal-call premise. -/
theorem deployment_safe (d : IR) (r : Node) (R : SC26.Roles) (cap : Nat)
    (ops : List SC26.Op) (actualEdges : List Edge) (sinkEffects : List (Nat × SC26.Tx))
    (h : Accepted d) (extraction : ExtractionFaithful d r actualEdges)
    (refinement : ProtocolRefinement d r R cap ops sinkEffects) :
    (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧
    (∀ e ∈ sinkEffects, ∃ req, SC26.reqOf (SC26.run R cap SC26.full SC26.init ops) e.1 = some req ∧
      req.tx = e.2 ∧ e.1 ∈ (SC26.run R cap SC26.full SC26.init ops).reserved ∧
      SC26.Approved R (SC26.run R cap SC26.full SC26.init ops) e.1 req) ∧
    (sinkEffects.map Prod.fst).Nodup ∧ (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧
    sinkEffects.length ≤ cap := by
  have legal : ∀ o ∈ ops, SC26.legal R o := by
    intro o ho
    cases o with
    | bankCall c k tx =>
      obtain ⟨a, ha, agent, hc⟩ := refinement.callerBinding c k tx ho
      change c ≠ R.gate
      rw [refinement.gateUID, hc]
      exact agent_not_receiver_uid d h r a extraction.receiverNode extraction.receiverID ha agent
    | request c tx => trivial
    | approve c k tx => trivial
    | execute c k => trivial
    | deliver k => trivial
    | arrive k => trivial
    | halt c => trivial
  have good := protocol_safe R cap ops legal
  refine ⟨fun e he ha hs => runtime_exclusive d actualEdges h extraction.authority e he ha hs, ?_⟩
  have unit_sum : ∀ xs : List (Nat × SC26.Tx),
      (∀ e ∈ xs, e.2.amount = 1) → (xs.map (fun e => e.2.amount)).sum = xs.length := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons e es ih =>
      intro hu
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [hu e List.mem_cons_self, ih (fun x hx => hu x (List.mem_cons_of_mem _ hx))]
      omega
  have bound : (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap := by
    rw [refinement.publication]
    exact good.2.2
  refine ⟨?_, ?_, bound, ?_⟩
  · rw [refinement.publication]; exact good.1
  · rw [refinement.publication]; exact good.2.1
  · simpa [unit_sum sinkEffects refinement.unitCosts] using bound

/-- Useful two-agent contract instance; both contend for one shared capacity. -/
def clean : IR := ⟨[⟨0,23701,true,false,false,0,true⟩, ⟨1,23702,true,false,false,0,true⟩,
    ⟨2,23700,false,false,false,1,true⟩, ⟨3,23700,false,false,false,2,true⟩,
    ⟨6,23703,false,false,false,3,true⟩, ⟨7,23704,false,false,false,4,true⟩],
    [⟨3,4,true,false,true⟩, ⟨2,5,true,false,true⟩, ⟨3,5,true,false,true⟩], 3,2,4,5⟩

theorem clean_accepted : Accepted clean := by decide

def twoRoles : SC26.Roles := ⟨[23701,23702],[23703],[23704],23700⟩
def payload : SC26.Tx := ⟨7,1,11⟩

theorem useful_acceptance :
    (SC26.run twoRoles 1 SC26.full SC26.init
      [.request 23701 payload, .approve 23703 0 payload, .execute 23701 0,
       .deliver 0, .arrive 0, .request 23702 payload, .approve 23703 1 payload,
       .execute 23702 1, .deliver 1, .arrive 1]).bank = [(0,payload)] := by decide

theorem writable_mount_refutes :
    ¬ Accepted {clean with edges := ⟨0,4,true,false,true⟩ :: clean.edges} := by decide

theorem unknown_refutes :
    ¬ Accepted {clean with edges := ⟨0,4,true,true,true⟩ :: clean.edges} := by decide

/-- Existing disabled payload guard counterexample, retained verbatim in its
own module; this alias proves reuse and gives a falsifiable contract instance. -/
theorem check_disabled_counterexample :
    let s := SC26.run SC26.R0 20 {SC26.full with payload := false} SC26.init
      [.request 1 SC26.tx1, .approve 2 0 SC26.tx2, .execute 1 0, .deliver 0, .arrive 0]
    s.bank = [(0,SC26.tx1)] ∧ s.approvals = [(0,2,SC26.tx2)] ∧ ¬ SC26.Good SC26.R0 20 s :=
  SC26.payload_unchecked_breaks

/-- Disabling the reused gate nonce guard makes reservation history nonunique,
while receiver deduplication still prevents duplicate sink effects. -/
theorem nonce_disabled_counterexample :
    let s := SC26.run SC26.R0 20 {SC26.full with nonce := false} SC26.init
      [.request 1 SC26.tx1, .approve 2 0 SC26.tx1, .execute 1 0, .execute 1 0]
    s.reserved = [0,0] ∧ ¬ s.reserved.Nodup := by decide

end ControlStack.Deployment
#print axioms ControlStack.Deployment.exclusive_sink
#print axioms ControlStack.Deployment.database_custody
#print axioms ControlStack.Deployment.runtime_exclusive
#print axioms ControlStack.Deployment.agent_not_receiver_uid
#print axioms ControlStack.Deployment.agent_call_legal
#print axioms ControlStack.Deployment.protocol_safe
#print axioms ControlStack.Deployment.one_use
#print axioms ControlStack.Deployment.gate_contract
#print axioms ControlStack.Deployment.broker_contract
#print axioms ControlStack.Deployment.clean_accepted
#print axioms ControlStack.Deployment.useful_acceptance
#print axioms ControlStack.Deployment.writable_mount_refutes
#print axioms ControlStack.Deployment.unknown_refutes
#print axioms ControlStack.Deployment.check_disabled_counterexample

#print axioms ControlStack.Deployment.deployment_safe

#print axioms ControlStack.Deployment.nonce_disabled_counterexample
