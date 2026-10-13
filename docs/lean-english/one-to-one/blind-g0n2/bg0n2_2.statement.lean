namespace PL_bg0n2_2
open ControlStack.TrustedBroker
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_transaction_preserves : Prop :=
  ∀ (roles : Roles) (s t : State),
    Safe s → Step roles s t → Safe t

def BackConclusion (roles : Roles) (s t : State) : Prop :=
  Safe t

def OrigConclusion (roles : Roles) (s t : State) : Prop :=
  Safe t

def OrigSignature : Prop :=
  ∀ (roles : Roles) (s t : State), Safe s → Step roles s t → Safe t

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.TrustedBroker.transaction_preserves

def Claim : Prop :=
  (Back_transaction_preserves = (∀ (roles : Roles) (s t : State), Safe s → Step roles s t → BackConclusion roles s t)) ∧
  (OrigSignature = (∀ (roles : Roles) (s t : State), Safe s → Step roles s t → OrigConclusion roles s t)) ∧
  (∀ (roles : Roles) (s t : State), Safe s → Step roles s t → (BackConclusion roles s t ↔ OrigConclusion roles s t))

def Witness : Prop :=
  ∃ (roles : Roles) (s t : State), Safe s ∧ Step roles s t ∧ s.spent < t.spent

end PL_bg0n2_2
