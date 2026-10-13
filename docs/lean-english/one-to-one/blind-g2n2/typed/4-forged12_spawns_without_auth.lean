import ControlStack.Scenarios.AuthInstancesB

namespace ControlStack.AuthInstances

def Back_forged12_spawns_without_auth : Prop :=
  let unguarded := ControlStack.AuthenticatedLog.authRun
    (SC12.step [9] SC12.full) (fun _ => (none : Option ℕ)) SC12.init forged12;
  let guarded := ControlStack.AuthenticatedLog.authRun
    (SC12.step [9] SC12.full) claim12 SC12.init forged12;
  unguarded.live.length = 2 ∧ guarded = SC12.init

end ControlStack.AuthInstances
