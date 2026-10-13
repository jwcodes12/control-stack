import ControlStack.Scenarios.SC23Injection

namespace ControlStack.SC23

-- Good is exactly the conjunction of confirmation correctness for
-- sensitive provenance-true actions and no repeated used confirmation.
def Back_sc23_safe : Prop :=
  ∀ (P : Policy) (ops : List Op), Good P (run P full init ops)

end ControlStack.SC23
