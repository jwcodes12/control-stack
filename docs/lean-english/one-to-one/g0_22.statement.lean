namespace PL_g0_22
open ControlStack ControlStack.Deployment
def Back (t : TrustedBroker.State) : Prop := t.spent ≤ t.cap ∧ t.releases ≤ t.spent ∧ t.consumed.Nodup ∧ ∀ k l, t.leases k = some l → l.used ≤ l.budget
def Orig (t : TrustedBroker.State) : Prop := TrustedBroker.Safe t
def Claim : Prop := ∀ (t : TrustedBroker.State), (Back t ↔ Orig t)
def Witness : Prop := Accepted clean
end PL_g0_22
