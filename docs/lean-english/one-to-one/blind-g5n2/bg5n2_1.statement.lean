namespace PL_bg5n2_1
open ControlStack.SC23Isolation
def Back_noninterference : Prop :=
  ∀ (E : Env) (ops ops' : List Op),
    List.Forall₂ SameExceptContent ops ops' →
      Rel (run E full init ops) (run E full init ops')

def Claim : Prop :=
  (Back_noninterference = (∀ (E : Env) (ops ops' : List Op),
    List.Forall₂ SameExceptContent ops ops' → Rel (run E full init ops) (run E full init ops'))) ∧
  (∀ (E : Env) (ops ops' : List Op), List.Forall₂ SameExceptContent ops ops' →
    (Rel (run E full init ops) (run E full init ops') ↔
     Rel (run E full init ops) (run E full init ops')))
def BasicWitness : Prop :=
  List.Forall₂ SameExceptContent
    ([.toolResult 66, .derive, .act 5 [1] 0] : List Op)
    [.toolResult 0, .derive, .act 5 [1] 0] ∧
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[41],false,none⟩]

def LimitWitness : Prop :=
  List.Forall₂ SameExceptContent
    ([.toolResult 66,.confirm 1 7 5 [66],.act 5 [0] 7] : List Op)
    [.toolResult 0,.confirm 1 7 5 [66],.act 5 [0] 7] ∧
  (run E0 full init [.toolResult 66,.confirm 1 7 5 [66],.act 5 [0] 7]).executed = [⟨5,[66],true,some 7⟩] ∧
  (run E0 full init [.toolResult 0,.confirm 1 7 5 [66],.act 5 [0] 7]).executed = []
def Witness : Prop := BasicWitness ∧ LimitWitness
end PL_bg5n2_1
