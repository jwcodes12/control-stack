namespace PL_bg5n1_9
open ControlStack.SC23
open scoped BigOperators

def Back_sc23_safe : Prop :=
  ∀ (P : Policy) (ops : List Op), Good P (run P full init ops)

def HBack (P : Policy) (ops : List Op) : Prop :=
  True
def HOrig (P : Policy) (ops : List Op) : Prop :=
  True
noncomputable def BackAt (P : Policy) (ops : List Op) : Prop :=
  Good P (run P full init ops)
noncomputable def OrigAt (P : Policy) (ops : List Op) : Prop :=
  Good P (run P full init ops)

def wPolicy : Policy := ⟨[1], [9], [7]⟩
def wOps : List Op := [.toolResult 0 42, .confirm 1 3 7 [42], .act 7 [0] 3]
def Witness : Prop := (run wPolicy full init wOps).executed = [⟨7, [42], true, some 3⟩] ∧ (run wPolicy full init wOps).used = [3]

def Claim : Prop :=
  (Back_sc23_safe ↔ ∀ (P : Policy) (ops : List Op), HBack P ops → BackAt P ops) ∧
  (∀ (P : Policy) (ops : List Op), HBack P ops ↔ HOrig P ops) ∧
  (∀ (P : Policy) (ops : List Op), HBack P ops → (BackAt P ops ↔ OrigAt P ops))
end PL_bg5n1_9
