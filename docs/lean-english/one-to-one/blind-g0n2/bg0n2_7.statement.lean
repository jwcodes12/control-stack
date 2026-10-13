namespace PL_bg0n2_7
open ControlStack.Deployment.TranscriptReplay
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_replay_was_not_allowed : Prop :=
  ∀ (now : Nat) (a' : ControlStack.TrustedBroker.Approval)
    (l' : ControlStack.TrustedBroker.Lease),
    ¬ ControlStack.TrustedBroker.Allowed R s8 now q8 a' l'

def BackConclusion (now : Nat) (a' : Approval) (l' : Lease) : Prop :=
  ¬ TrustedBroker.Allowed R s8 now q8 a' l'

def OrigConclusion (now : Nat) (a' : Approval) (l' : Lease) : Prop :=
  ¬ TrustedBroker.Allowed R s8 now q8 a' l'

def OrigSignature : Prop :=
  ∀ (now : Nat) (a' : Approval) (l' : Lease), ¬ TrustedBroker.Allowed R s8 now q8 a' l'

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.Deployment.TranscriptReplay.replay_was_not_allowed

def Claim : Prop :=
  (Back_replay_was_not_allowed = (∀ (now : Nat) (a' : Approval) (l' : Lease), BackConclusion now a' l')) ∧
  (OrigSignature = (∀ (now : Nat) (a' : Approval) (l' : Lease), OrigConclusion now a' l')) ∧
  (∀ (now : Nat) (a' : Approval) (l' : Lease), (BackConclusion now a' l' ↔ OrigConclusion now a' l'))

def Witness : Prop :=
  q8 = q7 ∧ s8 = committed s7 q7 a1 l1 ∧ Allowed R s7 ControlStack.Deployment.TranscriptReplay.now q7 a1 l1 ∧ s8.approvals 1 = some {a1 with used := true}

end PL_bg0n2_7
