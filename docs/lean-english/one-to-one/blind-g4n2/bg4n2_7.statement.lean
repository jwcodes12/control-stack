namespace ControlStack.SC20

-- Good admits only registered digests or digests in listed-reviewer promotions.
def Back_sc20_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    Good E (run E full init ops)

end ControlStack.SC20

namespace PL_bg4n2_7
open ControlStack.SC20
def BackPoint (E : Env) (s : St) : Prop := Good E s
def OrigPoint (E : Env) (s : St) : Prop := Good E s
def Claim : Prop := ∀ E s, BackPoint E s ↔ OrigPoint E s
def Witness : Prop := (run E0 full init [.agentWrite 1 1 66, .promote 2 1, .freeze 9 [1], .train]).trained = [[(1, 66)]]

end PL_bg4n2_7
