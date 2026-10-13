namespace ControlStack.SC19

-- Good uses DestroyOk: actual count, matching target/version snapshot,
-- a recorded verified index, an independent listed approver, and unique ids.
-- In this run, only a verifier-listed caller can add a verified index.
def Back_sc19_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    Good E (run E full init ops)

end ControlStack.SC19

namespace PL_bg4n2_3
open ControlStack.SC19
def BackPoint (E : Env) (s : St) : Prop := Good E s
def OrigPoint (E : Env) (s : St) : Prop := Good E s
def Claim : Prop := ∀ E s, BackPoint E s ↔ OrigPoint E s
def Witness : Prop := (run E0 full init [.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .commit 0 0]).destroyed = [⟨0, 1, 7, 1, 5, 0⟩]

end PL_bg4n2_3
