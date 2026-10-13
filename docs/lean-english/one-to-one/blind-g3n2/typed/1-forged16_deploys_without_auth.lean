import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

open ControlStack.AuthenticatedLog

-- The fixed forged trace, with claim checking disabled versus enabled.
def Back_forged16_deploys_without_auth : Prop :=
  (authRun (SC16.step SC16.R0 (fun x => x) SC16.full)
    (fun _ => none) SC16.init forged16).deployed =
      [⟨0, 5, 7⟩] ∧
  (authRun (SC16.step SC16.R0 (fun x => x) SC16.full)
    claim16 SC16.init forged16).deployed = []

end ControlStack.AuthInstances
