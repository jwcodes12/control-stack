namespace PL_bg3n2_1
open ControlStack.AuthInstances ControlStack
open ControlStack.AuthenticatedLog

def BackClosed : Prop :=
  (authRun (SC16.step SC16.R0 (fun x => x) SC16.full)
    (fun _ => none) SC16.init forged16).deployed =
      [⟨0, 5, 7⟩] ∧
  (authRun (SC16.step SC16.R0 (fun x => x) SC16.full)
    claim16 SC16.init forged16).deployed = []

def OrigAt : Prop :=
  (authRun (SC16.step SC16.R0 id SC16.full) (fun _ => none) SC16.init forged16).deployed = [⟨0, 5, 7⟩] ∧
  (authRun (SC16.step SC16.R0 id SC16.full) claim16 SC16.init forged16).deployed = []

def OrigClosed : Prop := OrigAt
def OriginalDeclaration : OrigClosed := @ControlStack.AuthInstances.forged16_deploys_without_auth

def Claim : Prop :=
  BackClosed ↔ OrigAt

def Witness : Prop :=
  BackClosed

end PL_bg3n2_1
