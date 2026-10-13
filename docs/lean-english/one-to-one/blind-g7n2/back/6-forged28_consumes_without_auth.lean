import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

def Back_forged28_consumes_without_auth : Prop :=
  let unchecked := SC28.run [9] 1000 SC28.full SC28.init
    (forged28.map Prod.snd)
  let checked := AuthenticatedLog.authRun
    (SC28.step [9] 1000 SC28.full) claim28 SC28.init forged28
  SC28.budgetOf unchecked 0 = some 100 ∧
    SC28.leaseOf unchecked 1 = some 0 ∧
    SC28.usedL unchecked 0 = 5 ∧
    Authenticated.applied claim28 forged28 = [SC28.Op.work 1 5 5] ∧
    SC28.usedT checked = 0

end ControlStack.AuthInstances
