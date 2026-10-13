namespace PL_bg0n2_3
open ControlStack.TrustedBroker
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_transaction_coherent : Prop :=
  ∀ (roles : Roles) (s t : State),
    Coherent s → Step roles s t → Coherent t

def BackConclusion (roles : Roles) (s t : State) : Prop :=
  Coherent t

def OrigConclusion (roles : Roles) (s t : State) : Prop :=
  Coherent t

def OrigSignature : Prop :=
  ∀ (roles : Roles) (s t : State), Coherent s → Step roles s t → Coherent t

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.TrustedBroker.transaction_coherent

def Claim : Prop :=
  (Back_transaction_coherent = (∀ (roles : Roles) (s t : State), Coherent s → Step roles s t → BackConclusion roles s t)) ∧
  (OrigSignature = (∀ (roles : Roles) (s t : State), Coherent s → Step roles s t → OrigConclusion roles s t)) ∧
  (∀ (roles : Roles) (s t : State), Coherent s → Step roles s t → (BackConclusion roles s t ↔ OrigConclusion roles s t))

def Witness : Prop :=
  ∃ (roles : Roles) (s t : State), Coherent s ∧ Step roles s t ∧ 1 ∉ s.consumed ∧ 1 ∈ t.consumed

end PL_bg0n2_3
