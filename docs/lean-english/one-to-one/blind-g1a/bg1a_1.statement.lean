namespace PL_bg1a_1
open ControlStack.EgressGate

def Back_step_safe : Prop :=
  ∀ (p : Policy) (s : State) (a : Action),
    Invariant p s → Invariant p (step p s a)

def peer : Peer := ⟨"peer", 443, "tcp"⟩
def policy : Policy := [⟨"authority", peer⟩]
def topology : Topology := ⟨true, true, true, true, true⟩
def start : State := ⟨true, topology, true, []⟩
def BackAt (p : Policy) (s : State) (a : Action) : Prop :=
  Invariant p (step p s a)
def OrigAt (p : Policy) (s : State) (a : Action) : Prop :=
  Invariant p (step p s a)

def Claim : Prop :=
  (Back_step_safe = (∀ (p : Policy) (s : State) (a : Action) (_h : Invariant p s), BackAt p s a)) ∧
  (∀ (p : Policy) (s : State) (a : Action) (_h : Invariant p s), BackAt p s a ↔ OrigAt p s a)

def Witness : Prop :=
  Invariant policy start ∧
  (step policy start (.request "authority")).attempts = [⟨.gateway, peer⟩]
end PL_bg1a_1
