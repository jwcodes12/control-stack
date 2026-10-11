import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_25
open ControlStack ControlStack.Deployment
def Back (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) : Prop := ¬ TrustedBroker.Allowed TranscriptReplay.R TranscriptReplay.s8 now TranscriptReplay.q8 a l
def Orig (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) : Prop := ¬ TrustedBroker.Allowed TranscriptReplay.R TranscriptReplay.s8 now TranscriptReplay.q8 a l
def Claim : Prop := ∀ (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease), (Back now a l ↔ Orig now a l)
def Witness : Prop := Accepted clean
end PL_g0_25

namespace ReviewProof_g0_25
open PL_g0_25
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro now a l
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) : Orig now a l := TranscriptReplay.replay_was_not_allowed now a l

end ReviewProof_g0_25
#print axioms ReviewProof_g0_25.claim
#print axioms ReviewProof_g0_25.witness
