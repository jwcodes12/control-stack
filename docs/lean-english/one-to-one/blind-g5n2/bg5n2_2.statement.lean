namespace PL_bg5n2_2
open ControlStack.SC23Isolation
def Back_w1_impossible : Prop :=
  let injected : List Op := [.toolResult 66, .derive, .act 5 [1] 0]
  let clean : List Op := [.toolResult 0, .derive, .act 5 [1] 0]
  let s := run E0 full init injected
  s.executed = (run E0 full init clean).executed ∧
    s.executed = [⟨5, [41], false, none⟩]

def Orig : Prop :=
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed =
    (run E0 full init [.toolResult 0, .derive, .act 5 [1] 0]).executed ∧
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[41],false,none⟩]
def Claim : Prop := Back_w1_impossible ↔ Orig
def Witness : Prop := (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[41],false,none⟩]
end PL_bg5n2_2
