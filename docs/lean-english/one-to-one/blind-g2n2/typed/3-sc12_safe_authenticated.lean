import ControlStack.Scenarios.AuthInstancesB

namespace ControlStack.AuthInstances

-- NOTE
-- AMBIGUOUS: The English does not explicitly specify the starting state.
-- This statement uses SC12.init for the run from the model's empty state.
-- An arbitrary starting state would need additional safety and provenance premises.
def Back_sc12_safe_authenticated : Prop :=
  ∀ (admins U : List ℕ) (ops : List (ℕ × SC12.Op)),
    (∀ u ∈ U, u ∉ admins) →
      let s := ControlStack.AuthenticatedLog.authRun
        (SC12.step admins SC12.full) claim12 SC12.init ops;
      SC12.Good s ∧
        ∀ e ∈ s.live, ∃ c : ℕ,
          c ∈ admins ∧ c ∉ U ∧ (c, SC12.Op.start c e.origin) ∈ ops

end ControlStack.AuthInstances
