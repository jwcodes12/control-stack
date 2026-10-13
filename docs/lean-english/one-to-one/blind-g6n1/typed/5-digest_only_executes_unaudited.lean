import ControlStack.Scenarios.SC25Content

namespace ControlStack.SC25Content

open ControlStack.SC25

-- NOTE
-- AMBIGUOUS: The single trace's operation id and submitted `declared` label
-- are not specified. This witness chooses id 0 and declared = false;
-- another reading uses a different fixed id or declared = true.
-- The deployed trusted classifier ignores the declared label.
def Back_digest_only_executes_unaudited : Prop :=
  let ops : List Op :=
    [.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .check 0, .fire 0]
  let sg := grun R0 (fun _ => 0) cls0 ops
  (∃ e ∈ sg.1.executed, e.content = 50) ∧
    sg.2 = [(0, 7, true, 2)]

end ControlStack.SC25Content
