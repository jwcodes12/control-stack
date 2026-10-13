import ControlStack.Scenarios.SC28Liveness

namespace ControlStack.SC28Liveness

open ControlStack.SC28

-- NOTE
-- The example reports actual units on both work steps. The English does
-- not specify reported costs; full ignores them, so this choice does not
-- change acceptance, charges, or usage.
def Back_global_cap_blocks_honest : Prop :=
  let s := run [9] 10 full init
    [Op.issue 9 0 10, Op.issue 9 1 10,
     Op.assignTo 9 1 0, Op.assignTo 9 2 1, Op.work 2 10 10]
  spentL s 0 = 0 ∧
    (step [9] 10 full s (.work 1 1 1)).usage = s.usage ∧
    (step [9] 10 full s (.work 1 1 1)).usage = [(2, 1, 10)]

end ControlStack.SC28Liveness
