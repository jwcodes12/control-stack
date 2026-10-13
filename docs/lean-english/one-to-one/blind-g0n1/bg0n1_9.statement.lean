namespace PL_bg0n1_9
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (d larger : IR) (start target : Nat),
    (∀ e ∈ d.edges, e ∈ larger.edges) →
    d.broker = larger.broker → d.receiver = larger.receiver →
    AvoidedPath d start target → AvoidedPath larger start target

def Orig : Prop :=
  ∀ (d larger : IR)
    (subset : ∀ e ∈ d.edges, e ∈ larger.edges)
    (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver)
    (start target : Nat) (path : AvoidedPath d start target),
    AvoidedPath larger start target

def BackConclusion (larger : IR) (start target : Nat) : Prop :=
  AvoidedPath larger start target

def OrigConclusion (larger : IR) (start target : Nat) : Prop :=
  AvoidedPath larger start target

def Claim : Prop :=
  (Back ↔ (∀ (d larger : IR) (start target : Nat),
    (∀ e ∈ d.edges, e ∈ larger.edges) →
    d.broker = larger.broker → d.receiver = larger.receiver →
    AvoidedPath d start target → BackConclusion larger start target)) ∧
  (Orig ↔ (∀ (d larger : IR)
    (subset : ∀ e ∈ d.edges, e ∈ larger.edges)
    (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver)
    (start target : Nat) (path : AvoidedPath d start target),
    OrigConclusion larger start target)) ∧
  (∀ (d larger : IR) (start target : Nat), (∀ e ∈ d.edges, e ∈ larger.edges) → d.broker = larger.broker → d.receiver = larger.receiver → AvoidedPath d start target →
    (BackConclusion larger start target ↔ OrigConclusion larger start target))

def Witness : Prop :=
  (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ sinkOnly.broker = clean.broker ∧ sinkOnly.receiver = clean.receiver ∧ AvoidedPath sinkOnly 3 4 ∧ 3 ≠ (4 : Nat) ∧ sinkOnly.edges ≠ clean.edges

end PL_bg0n1_9
