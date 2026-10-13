namespace PL_bg0n2_4
open ControlStack.TrustedBroker
open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay

def Back_committed_nonce_unusable : Prop :=
  ∀ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease)
    (r' : Request) (now : Nat) (a' : Approval) (l' : Lease),
    r'.nonce = r.nonce →
      ¬ Allowed roles (committed s r a l) now r' a' l'

def BackConclusion (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (r' : Request) (now : Nat) (a' : Approval) (l' : Lease) : Prop :=
  ¬ Allowed roles (committed s r a l) now r' a' l'

def OrigConclusion (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (r' : Request) (now : Nat) (a' : Approval) (l' : Lease) : Prop :=
  ¬ Allowed roles (committed s r a l) now r' a' l'

def OrigSignature : Prop :=
  ∀ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request) (a' : Approval) (l' : Lease), r'.nonce = r.nonce → ¬ Allowed roles (committed s r a l) now r' a' l'

theorem originalSignatureChecked : OrigSignature :=
  @ControlStack.TrustedBroker.committed_nonce_unusable

def Claim : Prop :=
  (Back_committed_nonce_unusable = (∀ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (r' : Request) (now : Nat) (a' : Approval) (l' : Lease), r'.nonce = r.nonce → BackConclusion roles s r a l r' now a' l')) ∧
  (OrigSignature = (∀ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request) (a' : Approval) (l' : Lease), r'.nonce = r.nonce → OrigConclusion roles s r a l r' now a' l')) ∧
  (∀ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (r' : Request) (now : Nat) (a' : Approval) (l' : Lease), r'.nonce = r.nonce → (BackConclusion roles s r a l r' now a' l' ↔ OrigConclusion roles s r a l r' now a' l'))

def Witness : Prop :=
  ∃ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request), Allowed roles s now r a l ∧ r'.nonce = r.nonce ∧ 0 < r.cost ∧ ¬ Allowed roles (committed s r a l) now r' a l

end PL_bg0n2_4
