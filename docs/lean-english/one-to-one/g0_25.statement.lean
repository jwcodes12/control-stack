namespace PL_g0_25
open ControlStack ControlStack.Deployment
def Back (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) : Prop := ¬ TrustedBroker.Allowed TranscriptReplay.R TranscriptReplay.s8 now TranscriptReplay.q8 a l
def Orig (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) : Prop := ¬ TrustedBroker.Allowed TranscriptReplay.R TranscriptReplay.s8 now TranscriptReplay.q8 a l
def Claim : Prop := ∀ (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease), (Back now a l ↔ Orig now a l)
def Witness : Prop := Accepted clean
end PL_g0_25
