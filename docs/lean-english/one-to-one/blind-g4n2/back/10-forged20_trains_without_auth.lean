namespace ControlStack.AuthInstances

def Back_forged20_trains_without_auth : Prop :=
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC20.step ControlStack.SC20.E0 ControlStack.SC20.full)
    (fun _ => none) ControlStack.SC20.init forged20).trained = [[(1, 66)]] ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC20.step ControlStack.SC20.E0 ControlStack.SC20.full)
    claim20 ControlStack.SC20.init forged20).trained = []

end ControlStack.AuthInstances
