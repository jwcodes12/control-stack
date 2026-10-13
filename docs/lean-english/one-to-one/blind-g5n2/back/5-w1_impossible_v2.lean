import ControlStack.Scenarios.SC23IsolationV2

namespace ControlStack.SC23IsolationV2

-- NOTE
-- AMBIGUOUS: The English trace does not specify the act operation's nonce.
-- This concrete trace uses nonce 0. There is no confirmation, and the derived
-- argument is untainted, so this nonce does not affect the stated execution.
def Back_w1_impossible_v2 : Prop :=
  let injected : List Op := [.toolResult 66, .derive, .act 5 [1] 0]
  let clean : List Op := [.toolResult 0, .derive, .act 5 [1] 0]
  let s := run E0 full init injected
  s.executed = (run E0 full init clean).executed ∧
    s.executed = [⟨5, [0], false, none⟩]

end ControlStack.SC23IsolationV2
