-- EXCERPT of ControlStack/EgressGate.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.
namespace ControlStack.EgressGate

structure Peer where
  address : String
  port : Nat
  protocol : String
  deriving DecidableEq, BEq

structure Rule where
  authority : String
  peer : Peer
  deriving DecidableEq, BEq

abbrev Policy := List Rule

def lookup (p : Policy) (key : String) : Option Peer :=
  match p with
  | [] => none
  | r :: rs => if r.authority = key then some r.peer else lookup rs key

structure Topology where
  noExternalRoute : Bool
  noInheritedAuthority : Bool
  privateNamespaces : Bool
  protectedPolicy : Bool
  noHostDeputy : Bool
  deriving DecidableEq

def safe (t : Topology) : Bool :=
  t.noExternalRoute && t.noInheritedAuthority && t.privateNamespaces &&
  t.protectedPolicy && t.noHostDeputy

inductive Origin where
  | gateway | sandbox
  deriving DecidableEq

structure Effect where
  origin : Origin
  peer : Peer

structure State where
  active : Bool
  topology : Topology
  gatewayUp : Bool
  attempts : List Effect

inductive Action where
  | launch (topology : Topology)
  | startGateway (supplied : Policy)
  | request (authority : String)
  | directAttempt (peer : Peer)
  | tamperPolicy
  | crashGateway

/-- Socket attempts, including failed connects, are effects. CONNECT tunnel bytes
are deliberately absent: they do not change the immediate peer. -/
def step (p : Policy) (s : State) : Action → State
  | .launch t => { s with active := safe t, topology := t }
  | .startGateway supplied => { s with gatewayUp := decide (supplied = p) }
  | .request key =>
    if s.active && s.gatewayUp then
      match lookup p key with
      | none => s
      | some peer => { s with attempts := s.attempts ++ [⟨.gateway, peer⟩] }
    else s
  | .directAttempt peer =>
    if s.active && !safe s.topology then
      { s with attempts := s.attempts ++ [⟨.sandbox, peer⟩] }
    else s
  | .tamperPolicy => s
  | .crashGateway => { s with gatewayUp := false }

def Invariant (p : Policy) (s : State) : Prop :=
  (s.active = true → safe s.topology = true) ∧
  ∀ e ∈ s.attempts, e.origin = .gateway ∧ e.peer ∈ p.map Rule.peer

def run (p : Policy) (s : State) (actions : List Action) : State :=
  actions.foldl (step p) s

end ControlStack.EgressGate

