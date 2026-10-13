namespace PL_bg1a_2
open ControlStack.EgressGate

def Back_trace_safe : Prop :=
  ∀ (p : Policy) (s : State) (actions : List Action),
    Invariant p s → Invariant p (run p s actions)

def peer : Peer := ⟨"peer", 443, "tcp"⟩
def policy : Policy := [⟨"authority", peer⟩]
def topology : Topology := ⟨true, true, true, true, true⟩
def start : State := ⟨true, topology, true, []⟩
def BackAt (p : Policy) (s : State) (actions : List Action) : Prop :=
  Invariant p (run p s actions)
def OrigAt (p : Policy) (s : State) (actions : List Action) : Prop :=
  Invariant p (run p s actions)

def Claim : Prop :=
  (Back_trace_safe = (∀ (p : Policy) (s : State) (actions : List Action) (_h : Invariant p s), BackAt p s actions)) ∧
  (∀ (p : Policy) (s : State) (actions : List Action) (_h : Invariant p s), BackAt p s actions ↔ OrigAt p s actions)

def Witness : Prop :=
  Invariant policy start ∧
  (step policy start (.request "authority")).attempts = [⟨.gateway, peer⟩]
end PL_bg1a_2
