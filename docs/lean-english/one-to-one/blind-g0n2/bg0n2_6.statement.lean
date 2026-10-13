namespace PL_bg0n2_6
open ControlStack.Deployment.TranscriptReplay
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_final_safe : Prop :=
  ControlStack.TrustedBroker.Safe s10

def BackConclusion  : Prop :=
  TrustedBroker.Safe s10

def OrigConclusion  : Prop :=
  TrustedBroker.Safe s10

def OrigSignature : Prop :=
  TrustedBroker.Safe s10

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.Deployment.TranscriptReplay.final_safe

def Claim : Prop :=
  (Back_final_safe = (BackConclusion )) ∧
  (OrigSignature = (OrigConclusion )) ∧
  ((BackConclusion  ↔ OrigConclusion ))

def Witness : Prop :=
  s10.spent = 2 ∧ s10.cap = 2 ∧ s10.releases = 2 ∧ s10.consumed = [2, 1] ∧ (s10.leases 1).map Lease.used = some 1 ∧ (s10.leases 2).map Lease.used = some 1

end PL_bg0n2_6
