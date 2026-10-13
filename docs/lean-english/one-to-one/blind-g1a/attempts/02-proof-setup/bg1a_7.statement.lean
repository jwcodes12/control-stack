namespace PL_bg1a_7
open ControlStack.SC06

def Back_halt_freezes : Prop :=
  ∀ (P : Policy) (s : St) (ops : List Op),
    s.halted = true → run P full s ops = s


def BackAt (P : Policy) (s : St) (ops : List Op) : Prop :=
  run P full s ops = s
def OrigAt (P : Policy) (s : St) (ops : List Op) : Prop :=
  run P full s ops = s

def Claim : Prop :=
  (Back_halt_freezes = (∀ (P : Policy) (s : St) (ops : List Op) (_hh : s.halted = true), BackAt P s ops)) ∧
  (∀ (P : Policy) (s : St) (ops : List Op) (_hh : s.halted = true), BackAt P s ops ↔ OrigAt P s ops)

def Witness : Prop :=
  let s := run P0 full init [.writeTyped 2 0 42 99, .read 2 0, .halt 9]
  s.halted = true ∧ s.ctx ≠ [] ∧
    run P0 full s [.writeTyped 1 1 9 9, .read 2 1, .confirm 5 3 2 7 42, .act 2 7 42 3, .halt 9] = s
end PL_bg1a_7
