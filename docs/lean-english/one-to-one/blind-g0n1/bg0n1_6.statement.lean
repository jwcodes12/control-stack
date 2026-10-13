namespace PL_bg0n1_6
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State),
    TrustedBroker.Trace R (TrustedBroker.initial cap) t →
    TrustedBroker.Safe t

def Orig : Prop :=
  ∀ (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State)
    (trace : TrustedBroker.Trace R (TrustedBroker.initial cap) t),
    TrustedBroker.Safe t

def BackConclusion (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State) : Prop :=
  TrustedBroker.Safe t

def OrigConclusion (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State) : Prop :=
  TrustedBroker.Safe t

def Claim : Prop :=
  (Back ↔ (∀ (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State),
    TrustedBroker.Trace R (TrustedBroker.initial cap) t →
    BackConclusion R cap t)) ∧
  (Orig ↔ (∀ (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State)
    (trace : TrustedBroker.Trace R (TrustedBroker.initial cap) t),
    OrigConclusion R cap t)) ∧
  (∀ (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State), TrustedBroker.Trace R (TrustedBroker.initial cap) t →
    (BackConclusion R cap t ↔ OrigConclusion R cap t))

def Witness : Prop :=
  TrustedBroker.Trace ControlStack.Deployment.Witnesses.R (TrustedBroker.initial 1) ControlStack.Deployment.Witnesses.s5 ∧ ControlStack.Deployment.Witnesses.s5.spent = 1 ∧ ControlStack.Deployment.Witnesses.s5.releases = 1 ∧ ControlStack.Deployment.Witnesses.s5.consumed = [7]

end PL_bg0n1_6
