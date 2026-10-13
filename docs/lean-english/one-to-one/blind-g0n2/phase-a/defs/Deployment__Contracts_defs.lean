-- EXCERPT of ControlStack/Deployment/Contracts.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.
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

/-- The kernel checks the same finite configuration obligations as Python.
Runtime flags are input observations, not independent attestation. -/
structure Accepted (d : IR) : Prop where
  basic : BaseAccepted d
  roles : RoleChecked d
  identities : IdentityChecked d
  runtime : ∀ n ∈ d.nodes, n.runtimeMatch = true
  writers : WritersChecked d
  bypass : NoBypass d

/-- Concrete runtime observations must be faithfully included in the IR;
this is the residual implementation/environment premise, not kernel-proved. -/
structure Faithful (d : IR) (actual : List Edge) : Prop where
  captured : ∀ e ∈ actual, e ∈ d.edges

/-- Role IDs are supplied as model parameters; actual SO_PEERCRED and human
role bindings are part of the residual faithful abstraction. -/
def roles (d : IR) (receiverUID : Nat) (approvers admins : List Nat) : SC26.Roles :=
  ⟨(d.nodes.filter (fun n => n.agent)).map Node.uid, approvers, admins, receiverUID⟩

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

/-- Useful two-agent contract instance; both contend for one shared capacity. -/
def clean : IR := ⟨[⟨0,23701,true,false,false,0,true⟩, ⟨1,23702,true,false,false,0,true⟩,
    ⟨2,23700,false,false,false,1,true⟩, ⟨3,23700,false,false,false,2,true⟩,
    ⟨6,23703,false,false,false,3,true⟩, ⟨7,23704,false,false,false,4,true⟩],
    [⟨3,4,true,false,true⟩, ⟨2,5,true,false,true⟩, ⟨3,5,true,false,true⟩], 3,2,4,5⟩

def twoRoles : SC26.Roles := ⟨[23701,23702],[23703],[23704],23700⟩
def payload : SC26.Tx := ⟨7,1,11⟩

end ControlStack.Deployment
