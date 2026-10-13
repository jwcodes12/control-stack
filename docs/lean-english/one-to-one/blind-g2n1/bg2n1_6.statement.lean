namespace PL_bg2n1_6
open ControlStack.SC09

def Back_sc09_halt_freezes : Prop :=
  ∀ (P : Policy) (s : St) (ops : List Op),
    s.halted = true → run P full s ops = s

def BackAt (P : Policy) (s : St) (ops : List Op) : Prop :=
  run P full s ops = s
def OrigAt (P : Policy) (s : St) (ops : List Op) : Prop :=
  run P full s ops = s
def Claim : Prop :=
  (Back_sc09_halt_freezes = (∀ P s ops, s.halted = true → BackAt P s ops)) ∧
  (∀ P s ops, s.halted = true → (BackAt P s ops ↔ OrigAt P s ops))
def Witness : Prop :=
  let s : St := ⟨[⟨1, 1, [7]⟩], [(1, 7)], [⟨1, 7, none⟩], true⟩
  s.halted = true ∧ s.procs ≠ [] ∧ s.granted ≠ [] ∧ s.used ≠ [] ∧
    run P0 full s [.start 9 2 1, .grant 9 1 1 8, .use 1 7, .halt 9] = s

end PL_bg2n1_6
