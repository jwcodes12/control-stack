namespace ControlStack.SC20

def Back_sc20_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true →
    run E full s ops = s

end ControlStack.SC20

namespace PL_bg4n2_8
open ControlStack.SC20
def BackPoint (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def OrigPoint (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def Claim : Prop := ∀ E s ops, s.halted = true → (BackPoint E s ops ↔ OrigPoint E s ops)
def Witness : Prop :=
  let s := run E0 full init [.ingest 50 0 7, .halt 9]
  s.halted = true ∧ s.store ≠ [] ∧ run E0 full s [.ingest 50 0 7, .agentWrite 1 1 66, .edit 1 77, .promote 2 1, .freeze 9 [1], .train] = s

end PL_bg4n2_8
