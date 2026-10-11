namespace PL_g0_20
open ControlStack.Deployment
def Back (R : ControlStack.TrustedBroker.Roles) (s t : ControlStack.TrustedBroker.State) : Prop := t = s
 def Orig (s t : ControlStack.TrustedBroker.State) : Prop := t.halted = true ∧ t.releases = s.releases
 def Claim : Prop := ∀ (R : ControlStack.TrustedBroker.Roles) (s t : ControlStack.TrustedBroker.State), s.halted = true → ControlStack.TrustedBroker.Step R s t → (Back R s t ↔ Orig s t)
 def Witness : Prop := Accepted clean
end PL_g0_20
