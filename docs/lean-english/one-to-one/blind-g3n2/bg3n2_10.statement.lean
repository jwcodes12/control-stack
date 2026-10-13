namespace PL_bg3n2_10
open ControlStack.AuthInstances ControlStack
open ControlStack.AuthenticatedLog

def BackClosed : Prop :=
  (authRun (SC17.step SC17.E0 SC17.full)
    (fun _ => none) (SC17.init []) forged17).live = [(1, 1, 1)] ∧
  (authRun (SC17.step SC17.E0 SC17.full)
    claim17 (SC17.init []) forged17).applied = []

def OrigAt : Prop :=
  (authRun (SC17.step SC17.E0 SC17.full) (fun _ => none) (SC17.init []) forged17).live = [(1, 1, 1)] ∧
  (authRun (SC17.step SC17.E0 SC17.full) claim17 (SC17.init []) forged17).applied = []

def OrigClosed : Prop := OrigAt
def OriginalDeclaration : OrigClosed := @ControlStack.AuthInstances.forged17_applies_without_auth

def Claim : Prop :=
  BackClosed ↔ OrigAt

def Witness : Prop :=
  BackClosed

end PL_bg3n2_10
