import ControlStack.Scenarios.SC08Exec

namespace ControlStack.SC08

-- NOTE
-- AMBIGUOUS: "The same safety statement" could carry over claim 1's
-- initially false halted flag, whereas "with no runs" imposes no condition
-- on that flag. This statement follows the latter reading and quantifies
-- the initial halted flag freely; the initial run list is empty.
def Back_safe_of_sound : Prop :=
  ∀ (E : Env) (C : Checks) (files : List (ℕ × ℕ))
    (halted : Bool) (ops : List Op),
    Sound C → Good E (run E C (⟨files, [], halted⟩ : St) ops)

end ControlStack.SC08
