namespace PL_bg2n1_9
open ControlStack.SC10

def Back_sc10_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

def BackAt (E : Env) (s : St) (ops : List Op) : Prop :=
  run E full s ops = s
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop :=
  run E full s ops = s
def Claim : Prop :=
  (Back_sc10_halt_freezes = (∀ E s ops, s.halted = true → BackAt E s ops)) ∧
  (∀ E s ops, s.halted = true → (BackAt E s ops ↔ OrigAt E s ops))
def Witness : Prop :=
  let s : St := ⟨[(5, 9)], some 0, 2, 3, [⟨1, some 0, 5, 1⟩], [40], true⟩
  s.halted = true ∧ s.versions ≠ [] ∧ s.decisions ≠ [] ∧ s.builds ≠ [] ∧
    run E0 full s [.writePolicy 9 6, .decide 2, .build, .halt 9] = s

end PL_bg2n1_9
