import ControlStack.Scenarios.AuthInstancesB

namespace ControlStack.AuthInstances

def Back_forged15_merges_without_auth : Prop :=
  let unchecked := AuthenticatedLog.authRun (SC15.step SC15.E0 SC15.full)
    (fun (_ : SC15.Op) => (none : Option ℕ)) SC15.init forged15
  let checked := AuthenticatedLog.authRun (SC15.step SC15.E0 SC15.full)
    claim15 SC15.init forged15
  0 ∈ unchecked.merged.map SC15.Change.id ∧ checked.merged = []

end ControlStack.AuthInstances
