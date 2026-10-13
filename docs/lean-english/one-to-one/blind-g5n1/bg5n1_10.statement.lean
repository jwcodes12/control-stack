namespace PL_bg5n1_10
open ControlStack.SC23
open scoped BigOperators

def Back_halt_freezes : Prop :=
  ∀ (P : Policy) (s : St) (ops : List Op),
    s.halted = true → run P full s ops = s

def HBack (P : Policy) (s : St) (ops : List Op) : Prop :=
  (s.halted = true)
def HOrig (P : Policy) (s : St) (ops : List Op) : Prop :=
  (s.halted = true)
noncomputable def BackAt (P : Policy) (s : St) (ops : List Op) : Prop :=
  run P full s ops = s
noncomputable def OrigAt (P : Policy) (s : St) (ops : List Op) : Prop :=
  run P full s ops = s

def wPolicy : Policy := ⟨[1], [9], [7]⟩
def wState : St := ⟨[⟨0, 42, true, true⟩], [⟨3, 7, [42], 1⟩], [3], [⟨7, [42], true, some 3⟩], true⟩
def wOps : List Op := [.userInput 1 99, .confirm 1 4 7 [99], .act 7 [0] 4, .halt 9]
def Witness : Prop := wState.halted = true ∧ wState.store ≠ [] ∧ wState.executed ≠ [] ∧ run wPolicy full wState wOps = wState

def Claim : Prop :=
  (Back_halt_freezes ↔ ∀ (P : Policy) (s : St) (ops : List Op), HBack P s ops → BackAt P s ops) ∧
  (∀ (P : Policy) (s : St) (ops : List Op), HBack P s ops ↔ HOrig P s ops) ∧
  (∀ (P : Policy) (s : St) (ops : List Op), HBack P s ops → (BackAt P s ops ↔ OrigAt P s ops))
end PL_bg5n1_10
