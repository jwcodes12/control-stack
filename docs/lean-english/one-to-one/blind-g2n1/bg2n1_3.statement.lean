namespace PL_bg2n1_3
open ControlStack.SC08

def Back_sc08_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

def BackAt (E : Env) (s : St) (ops : List Op) : Prop :=
  run E full s ops = s
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop :=
  run E full s ops = s
def Claim : Prop :=
  (Back_sc08_halt_freezes = (∀ E s ops, s.halted = true → BackAt E s ops)) ∧
  (∀ E s ops, s.halted = true → (BackAt E s ops ↔ OrigAt E s ops))
def Witness : Prop :=
  let s : St := ⟨[(1, 10)], [(10, none)], true⟩
  s.halted = true ∧ s.files ≠ [] ∧ s.ran ≠ [] ∧
    run E0 full s [.write 1 999, .exec 1 none, .halt 9] = s

end PL_bg2n1_3
