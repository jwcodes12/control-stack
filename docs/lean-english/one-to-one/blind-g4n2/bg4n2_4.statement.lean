namespace ControlStack.SC19

def Back_sc19_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true →
    run E full s ops = s

end ControlStack.SC19

namespace PL_bg4n2_4
open ControlStack.SC19
def BackPoint (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def OrigPoint (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def Claim : Prop := ∀ E s ops, s.halted = true → (BackPoint E s ops ↔ OrigPoint E s ops)
def Witness : Prop :=
  let s := run E0 full init [.write 7 5, .halt 9]
  s.halted = true ∧ s.objs ≠ [] ∧ run E0 full s [.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .commit 0 0] = s

end PL_bg4n2_4
