namespace PL_bg5n2_8
open ControlStack ControlStack.AuthInstances ControlStack.AuthenticatedLog
def Back_forged23_acts_without_auth : Prop :=
  (authRun (SC23.step SC23.P0 SC23.full)
      (fun (_ : SC23.Op) => none) SC23.init forged23).executed =
      [⟨5, [66], true, some 7⟩] ∧
    (authRun (SC23.step SC23.P0 SC23.full)
      claim23 SC23.init forged23).executed = []

def Orig : Prop :=
  (authRun (SC23.step SC23.P0 SC23.full) (fun _ => none) SC23.init forged23).executed = [⟨5,[66],true,some 7⟩] ∧
  (authRun (SC23.step SC23.P0 SC23.full) claim23 SC23.init forged23).executed = []
def Claim : Prop := Back_forged23_acts_without_auth ↔ Orig
def Witness : Prop :=
  forged23 = [(7,SC23.Op.toolResult 0 66),(7,SC23.Op.confirm 1 7 5 [66]),(7,SC23.Op.act 5 [0] 7)] ∧
  Back_forged23_acts_without_auth
end PL_bg5n2_8
