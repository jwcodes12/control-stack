namespace PL_bg3n1_4

open ControlStack.SC15 ControlStack.AuthInstances ControlStack.AuthenticatedLog

def BackClosed : Prop :=
  let unchecked := AuthenticatedLog.authRun (SC15.step SC15.E0 SC15.full)
    (fun (_ : SC15.Op) => (none : Option ℕ)) SC15.init forged15
  let checked := AuthenticatedLog.authRun (SC15.step SC15.E0 SC15.full)
    claim15 SC15.init forged15
  0 ∈ unchecked.merged.map SC15.Change.id ∧ checked.merged = []

def BackAt (unchecked checked : St) : Prop :=
  0 ∈ unchecked.merged.map Change.id ∧ checked.merged = []
def OrigAt (unchecked checked : St) : Prop :=
  unchecked.merged = [⟨0, 1, 7, [5], [5]⟩] ∧ checked.merged = []
def unchecked : St := authRun (step E0 full) (fun _ => none) init forged15
def checked : St := authRun (step E0 full) claim15 init forged15
def OrigClosed : Prop := OrigAt unchecked checked

def Claim : Prop :=
  (BackClosed ↔ BackAt unchecked checked) ∧
  (∀ u c, OrigAt u c → BackAt u c) ∧
  (∃ u c, BackAt u c ∧ ¬ OrigAt u c)

def Witness : Prop :=
  OrigAt unchecked checked ∧ unchecked.reviews ≠ [] ∧
  (∀ u c, OrigAt u c → BackAt u c)

end PL_bg3n1_4
