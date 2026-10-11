import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_21
open ControlStack ControlStack.Deployment
def Back (R : TrustedBroker.Roles) (s : TrustedBroker.State) (r : TrustedBroker.Request) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) (now : Nat) (q : TrustedBroker.Request) (b : TrustedBroker.Approval) (m : TrustedBroker.Lease) : Prop := ¬ TrustedBroker.Allowed R (TrustedBroker.committed s r a l) now q b m
def Orig (R : TrustedBroker.Roles) (s : TrustedBroker.State) (r : TrustedBroker.Request) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) (now : Nat) (q : TrustedBroker.Request) (b : TrustedBroker.Approval) (m : TrustedBroker.Lease) : Prop := ¬ TrustedBroker.Allowed R (TrustedBroker.committed s r a l) now q b m
def Claim : Prop := ∀ (R : TrustedBroker.Roles) (s : TrustedBroker.State) (r : TrustedBroker.Request) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) (now : Nat) (q : TrustedBroker.Request) (b : TrustedBroker.Approval) (m : TrustedBroker.Lease), (Back R s r a l now q b m ↔ Orig R s r a l now q b m)
def Witness : Prop := Accepted clean
end PL_g0_21

namespace ReviewProof_g0_21
open PL_g0_21
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R s r a l now q b m
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (s : TrustedBroker.State) (r : TrustedBroker.Request) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) (now : Nat) (q : TrustedBroker.Request) (b : TrustedBroker.Approval) (m : TrustedBroker.Lease) (same : q.nonce = r.nonce) : Orig R s r a l now q b m := TrustedBroker.committed_nonce_unusable R s r a l now q b m same

end ReviewProof_g0_21
#print axioms ReviewProof_g0_21.claim
#print axioms ReviewProof_g0_21.witness
