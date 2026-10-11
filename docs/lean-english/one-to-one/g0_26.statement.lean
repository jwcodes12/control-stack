namespace PL_g0_26
open ControlStack ControlStack.Deployment
def Back  : Prop := CheckedTrace.verified TranscriptReplay.table.step 0 (TranscriptReplay.receipts.take 9) = true
def Orig  : Prop := CheckedTrace.verified TranscriptReplay.table.step 0 TranscriptReplay.withoutLastRelease = true
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_26
