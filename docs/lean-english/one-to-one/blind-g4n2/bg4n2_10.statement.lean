namespace ControlStack.AuthInstances

def Back_forged20_trains_without_auth : Prop :=
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC20.step ControlStack.SC20.E0 ControlStack.SC20.full)
    (fun _ => none) ControlStack.SC20.init forged20).trained = [[(1, 66)]] ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC20.step ControlStack.SC20.E0 ControlStack.SC20.full)
    claim20 ControlStack.SC20.init forged20).trained = []

end ControlStack.AuthInstances

namespace PL_bg4n2_10
open ControlStack.SC20 ControlStack.AuthInstances ControlStack.AuthenticatedLog
def BackPoint (withoutAuth withAuth : List (List (ℕ × ℕ))) : Prop := withoutAuth = [[(1, 66)]] ∧ withAuth = []
def OrigPoint (withoutAuth withAuth : List (List (ℕ × ℕ))) : Prop := withoutAuth = [[(1, 66)]] ∧ withAuth = []
def Claim : Prop := ∀ withoutAuth withAuth, BackPoint withoutAuth withAuth ↔ OrigPoint withoutAuth withAuth
def Witness : Prop := Back_forged20_trains_without_auth

end PL_bg4n2_10
