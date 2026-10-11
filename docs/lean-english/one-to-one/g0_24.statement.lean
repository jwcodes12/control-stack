namespace PL_g0_24
open ControlStack ControlStack.Deployment
def Back  : Prop := TranscriptReplay.s10.spent ≤ TranscriptReplay.s10.cap ∧ TranscriptReplay.s10.releases ≤ TranscriptReplay.s10.spent ∧ TranscriptReplay.s10.consumed.Nodup ∧ ∀ k l, TranscriptReplay.s10.leases k = some l → l.used ≤ l.budget
def Orig  : Prop := TrustedBroker.Safe TranscriptReplay.s10
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_24
