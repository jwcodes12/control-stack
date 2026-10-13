namespace PL_bg0n2_8
open ControlStack.Deployment.TranscriptReplay
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_omitted_tail_is_accepted : Prop :=
  ControlStack.CheckedTrace.verified table.step 0 withoutLastRelease = true

def BackConclusion  : Prop :=
  CheckedTrace.verified table.step 0 withoutLastRelease = true

def OrigConclusion  : Prop :=
  CheckedTrace.verified table.step 0 withoutLastRelease = true

def OrigSignature : Prop :=
  CheckedTrace.verified table.step 0 withoutLastRelease = true

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.Deployment.TranscriptReplay.omitted_tail_is_accepted

def Claim : Prop :=
  (Back_omitted_tail_is_accepted = (BackConclusion )) ∧
  (OrigSignature = (OrigConclusion )) ∧
  ((BackConclusion  ↔ OrigConclusion ))

def Witness : Prop :=
  receipts.length = 10 ∧ withoutLastRelease.length = 9 ∧ withoutLastRelease ≠ [] ∧ CheckedTrace.recordedEnd 0 withoutLastRelease = 9 ∧ CheckedTrace.recordedEnd 0 receipts = 10 ∧ CheckedTrace.verified table.step 0 receipts = true ∧ CheckedTrace.verified table.step 0 withoutMiddleRelease = false ∧ CheckedTrace.verified table.step 0 withoutDenial = false

end PL_bg0n2_8
