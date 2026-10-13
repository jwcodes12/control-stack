namespace PL_bg1a_6
open ControlStack.SC06

def Back_sc06_safe : Prop :=
  ∀ (P : Policy) (ops : List Op),
    Good P (run P full init ops)


def BackAt (P : Policy) (ops : List Op) : Prop :=
  Good P (run P full init ops)
def OrigAt (P : Policy) (ops : List Op) : Prop :=
  Good P (run P full init ops)

def Claim : Prop :=
  (Back_sc06_safe = (∀ (P : Policy) (ops : List Op), BackAt P ops)) ∧
  (∀ (P : Policy) (ops : List Op), BackAt P ops ↔ OrigAt P ops)

def Witness : Prop :=
  (run P0 full init [.writeTyped 1 0 42 99, .read 2 0, .confirm 5 3 2 7 42, .act 2 7 42 3]).executed =
    [⟨2, 7, 42, true, some 3⟩]
end PL_bg1a_6
