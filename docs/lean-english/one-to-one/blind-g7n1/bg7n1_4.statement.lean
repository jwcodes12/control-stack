namespace PL_bg7n1_4
open ControlStack.SC27Chain


def FrozenBack : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

def BackAt (E : Env) (s : St) (ops : List Op) : Prop :=
  run E full s ops = s

def OrigAt (E : Env) (s : St) (ops : List Op) : Prop :=
  run E full s ops = s

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (s : St) (ops : List Op), s.halted = true → BackAt E s ops)) ∧
  (∀ (E : Env) (s : St) (ops : List Op), s.halted = true → (BackAt E s ops ↔ OrigAt E s ops))

def Witness : Prop :=
  let s := run E0 full init [.append 5, .anchor, .verify [5], .halt 9]
  s.halted = true ∧ s.accepted = [[5]] ∧
  run E0 full s [.append 6, .rewrite [7], .anchor, .writerAnchor 8, .verify [7], .halt 9] = s

end PL_bg7n1_4
