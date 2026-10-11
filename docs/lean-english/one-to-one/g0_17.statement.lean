namespace PL_g0_17
open ControlStack ControlStack.Deployment
def Back (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat) : Prop := TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))
def Orig (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat) : Prop := TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))
def Claim : Prop := ∀ (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat), (Back R table rs start ↔ Orig R table rs start)
def Witness : Prop := Accepted clean
end PL_g0_17
