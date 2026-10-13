namespace ControlStack.AuthInstances

def Back_forged19_destroys_without_auth : Prop :=
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC19.step ControlStack.SC19.E0 ControlStack.SC19.full)
    (fun _ => none) ControlStack.SC19.init forged19).destroyed =
      ([⟨0, 1, 7, 1, 5, 0⟩] : List ControlStack.SC19.Destroy) ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC19.step ControlStack.SC19.E0 ControlStack.SC19.full)
    claim19 ControlStack.SC19.init forged19).destroyed = []

end ControlStack.AuthInstances

namespace PL_bg4n2_6
open ControlStack.SC19 ControlStack.AuthInstances ControlStack.AuthenticatedLog
def BackPoint (withoutAuth withAuth : List Destroy) : Prop := withoutAuth = [⟨0, 1, 7, 1, 5, 0⟩] ∧ withAuth = []
def OrigPoint (withoutAuth withAuth : List Destroy) : Prop := withoutAuth = [⟨0, 1, 7, 1, 5, 0⟩] ∧ withAuth = []
def Claim : Prop := ∀ withoutAuth withAuth, BackPoint withoutAuth withAuth ↔ OrigPoint withoutAuth withAuth
def Witness : Prop := Back_forged19_destroys_without_auth

end PL_bg4n2_6
