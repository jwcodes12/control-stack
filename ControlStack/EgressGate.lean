import Std

/-! SC-03 pinned-peer model. The runtime correspondence obligations are listed in
`egress/FIDELITY.md`. This does not prove Linux isolation or HTTP parser correctness. -/

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

theorem lookup_pinned (p : Policy) (key : String) (peer : Peer)
    (h : lookup p key = some peer) : peer ∈ p.map Rule.peer := by
  induction p with
  | nil => simp [lookup] at h
  | cons r rs ih =>
    simp only [lookup] at h
    split at h
    · cases h
      simp
    · simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih h)

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

theorem direct_no_effect (p : Policy) (s : State) (peer : Peer)
    (h : Invariant p s) : step p s (.directAttempt peer) = s := by
  cases ha : s.active with
  | false => simp [step, ha]
  | true => simp [step, ha, h.1 ha]

theorem step_safe (p : Policy) (s : State) (a : Action)
    (h : Invariant p s) : Invariant p (step p s a) := by
  cases a with
  | launch t => exact ⟨fun ht => ht, h.2⟩
  | startGateway supplied => exact h
  | tamperPolicy => exact h
  | crashGateway => exact h
  | directAttempt peer => rw [direct_no_effect p s peer h]; exact h
  | request key =>
    simp only [step]
    split
    · cases hl : lookup p key with
      | none => exact h
      | some peer =>
        refine ⟨h.1, ?_⟩
        intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | he
        · exact h.2 e he
        · subst e
          exact ⟨rfl, lookup_pinned p key peer hl⟩
    · exact h

def run (p : Policy) (s : State) (actions : List Action) : State :=
  actions.foldl (step p) s

theorem trace_safe (p : Policy) (s : State) (actions : List Action)
    (h : Invariant p s) : Invariant p (run p s actions) := by
  induction actions generalizing s with
  | nil => exact h
  | cons a actions ih => exact ih (step p s a) (step_safe p s a h)

theorem failed_launch (p : Policy) (s : State) (t : Topology) (h : safe t = false) :
    (step p s (.launch t)).active = false := by simp [step, h]

theorem crash_closed (p : Policy) (s : State) (key : String) :
    (step p (step p s .crashGateway) (.request key)).attempts = s.attempts := by
  simp [step]

#print axioms lookup_pinned
#print axioms direct_no_effect
#print axioms step_safe
#print axioms trace_safe
#print axioms failed_launch
#print axioms crash_closed

end ControlStack.EgressGate
