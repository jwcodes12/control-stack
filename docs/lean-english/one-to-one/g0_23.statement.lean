namespace PL_g0_23
open ControlStack ControlStack.Deployment
def Back  : Prop := TrustedBroker.Trace TranscriptReplay.R (TrustedBroker.initial 2) TranscriptReplay.s10
def Orig  : Prop := TrustedBroker.Trace TranscriptReplay.R (TrustedBroker.initial 2) TranscriptReplay.s10
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_23
