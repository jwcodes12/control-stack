import ControlStack.TrustedBroker

namespace ControlStack.TrustedBroker

def Back_committed_nonce_unusable : Prop :=
  ∀ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease)
    (r' : Request) (now : Nat) (a' : Approval) (l' : Lease),
    r'.nonce = r.nonce →
      ¬ Allowed roles (committed s r a l) now r' a' l'

end ControlStack.TrustedBroker
