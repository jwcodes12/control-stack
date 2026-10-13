namespace PL_bg0n2_5
open ControlStack.TrustedBroker
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_trace_preserves : Prop :=
  ∀ (roles : Roles) (s t : State),
    Safe s → Trace roles s t → Safe t

def BackConclusion (roles : Roles) (s t : State) : Prop :=
  Safe t

def OrigConclusion (roles : Roles) (s t : State) : Prop :=
  Safe t

def OrigSignature : Prop :=
  ∀ (roles : Roles) (s t : State), Safe s → Trace roles s t → Safe t

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.TrustedBroker.trace_preserves

def Claim : Prop :=
  (Back_trace_preserves = (∀ (roles : Roles) (s t : State), Safe s → Trace roles s t → BackConclusion roles s t)) ∧
  (OrigSignature = (∀ (roles : Roles) (s t : State), Safe s → Trace roles s t → OrigConclusion roles s t)) ∧
  (∀ (roles : Roles) (s t : State), Safe s → Trace roles s t → (BackConclusion roles s t ↔ OrigConclusion roles s t))

def Witness : Prop :=
  ∃ (roles : Roles) (s t : State), Safe s ∧ Trace roles s t ∧ s.spent < t.spent ∧ t.releases = 2

end PL_bg0n2_5
