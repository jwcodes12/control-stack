namespace PL_bg0n2_1
open ControlStack.Deployment
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_indexed_receipts_sound : Prop :=
  ∀ (R : ControlStack.TrustedBroker.Roles) (table : IndexedBrokerTable R)
    (start : Nat) (rs : List (ControlStack.CheckedTrace.Receipt Nat Nat)),
    ControlStack.CheckedTrace.verified table.step start rs = true →
      ControlStack.TrustedBroker.Trace R (table.interpret start)
        (table.interpret (ControlStack.CheckedTrace.recordedEnd start rs))

def BackConclusion (R : Roles) (table : IndexedBrokerTable R) (start : Nat) (rs : List (CheckedTrace.Receipt Nat Nat)) : Prop :=
  TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))

def OrigConclusion (R : Roles) (table : IndexedBrokerTable R) (start : Nat) (rs : List (CheckedTrace.Receipt Nat Nat)) : Prop :=
  TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))

def OrigSignature : Prop :=
  ∀ (R : Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat), CheckedTrace.verified table.step start rs = true → TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.Deployment.indexed_receipts_sound

def Claim : Prop :=
  (Back_indexed_receipts_sound = (∀ (R : Roles) (table : IndexedBrokerTable R) (start : Nat) (rs : List (CheckedTrace.Receipt Nat Nat)), CheckedTrace.verified table.step start rs = true → BackConclusion R table start rs)) ∧
  (OrigSignature = (∀ (R : Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat), CheckedTrace.verified table.step start rs = true → OrigConclusion R table start rs)) ∧
  (∀ (R : Roles) (table : IndexedBrokerTable R) (start : Nat) (rs : List (CheckedTrace.Receipt Nat Nat)), CheckedTrace.verified table.step start rs = true → (BackConclusion R table start rs ↔ OrigConclusion R table start rs))

def Witness : Prop :=
  ∃ (R : Roles) (table : IndexedBrokerTable R) (start : Nat) (rs : List (CheckedTrace.Receipt Nat Nat)), rs ≠ [] ∧ CheckedTrace.verified table.step start rs = true ∧ (table.interpret start).spent < (table.interpret (CheckedTrace.recordedEnd start rs)).spent

end PL_bg0n2_1
