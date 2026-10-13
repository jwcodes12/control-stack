import ControlStack.Scenarios.SC28Refinement

namespace ControlStack.SC28Refinement

def Back_concrete_revoked_stops : Prop :=
  ∀ (G lid : ℕ) (first second : List COp),
    lid ∈ (runC G cinit first).revoked →
    counter (runC G (runC G cinit first) second) lid =
      counter (runC G cinit first) lid

end ControlStack.SC28Refinement
