import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

open ControlStack.SC25 ControlStack.AuthenticatedLog

def Back_forged25_executes_without_auth : Prop :=
  let plain := run R0 (fun x => x) cls0 full init (forged25.map Prod.snd)
  let guarded := authRun (step R0 (fun x => x) cls0 full) claim25 init forged25
  0 ∈ plain.executed.map Exec.id ∧ guarded.executed = []

end ControlStack.AuthInstances
