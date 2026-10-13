import ControlStack.Scenarios.AuthInstancesB

namespace ControlStack.AuthInstances

open ControlStack.AuthenticatedLog

-- The all-none claim function disables identity checks for this negative control.
def Back_forged23_acts_without_auth : Prop :=
  (authRun (SC23.step SC23.P0 SC23.full)
      (fun (_ : SC23.Op) => none) SC23.init forged23).executed =
      [⟨5, [66], true, some 7⟩] ∧
    (authRun (SC23.step SC23.P0 SC23.full)
      claim23 SC23.init forged23).executed = []

end ControlStack.AuthInstances
