namespace PL_g0_19
open ControlStack ControlStack.Deployment
def Back (t : TrustedBroker.State) : Prop := ∀ nonce, nonce ∈ t.consumed ↔ ∃ a, t.approvals nonce = some a ∧ a.used = true
def Orig (t : TrustedBroker.State) : Prop := TrustedBroker.Coherent t
def Claim : Prop := ∀ (t : TrustedBroker.State), (Back t ↔ Orig t)
def Witness : Prop := Accepted clean
end PL_g0_19
