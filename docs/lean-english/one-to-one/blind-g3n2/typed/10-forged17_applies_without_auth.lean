import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

open ControlStack.AuthenticatedLog

-- The unauthenticated outcome is about live; the authenticated one is
-- about applied, as specified by the English statement.
def Back_forged17_applies_without_auth : Prop :=
  (authRun (SC17.step SC17.E0 SC17.full)
    (fun _ => none) (SC17.init []) forged17).live = [(1, 1, 1)] ∧
  (authRun (SC17.step SC17.E0 SC17.full)
    claim17 (SC17.init []) forged17).applied = []

end ControlStack.AuthInstances
