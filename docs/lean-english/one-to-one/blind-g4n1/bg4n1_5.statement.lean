namespace PL_bg4n1_5
open ControlStack.AuthInstances

def Back_forged18_redirects_without_auth : Prop :=
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 5 ControlStack.SC18.full)
    (fun (_ : ControlStack.SC18.Op) => (none : Option ℕ))
    (ControlStack.SC18.init 0) forged18).cfg = 66 ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 5 ControlStack.SC18.full)
    claim18 (ControlStack.SC18.init 0) forged18).cfg = 0

def BackAt : Prop :=
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 5 ControlStack.SC18.full)
    (fun (_ : ControlStack.SC18.Op) => (none : Option ℕ))
    (ControlStack.SC18.init 0) forged18).cfg = 66 ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 5 ControlStack.SC18.full)
    claim18 (ControlStack.SC18.init 0) forged18).cfg = 0

def OrigAt : Prop :=
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 5 ControlStack.SC18.full)
    (fun (_ : ControlStack.SC18.Op) => (none : Option ℕ))
    (ControlStack.SC18.init 0) forged18).cfg = 66 ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 5 ControlStack.SC18.full)
    claim18 (ControlStack.SC18.init 0) forged18).cfg = 0

def Claim : Prop := (Back_forged18_redirects_without_auth ↔ BackAt) ∧ (BackAt ↔ OrigAt)

def Witness : Prop :=
  forged18 = [(1, ControlStack.SC18.Op.setSink 9 66)] ∧ BackAt

end PL_bg4n1_5
