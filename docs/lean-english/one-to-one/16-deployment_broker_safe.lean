import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_16
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (r : Node) (R : ControlStack.TrustedBroker.Roles) (cap : Nat) (t : ControlStack.TrustedBroker.State) (actual : List Edge) (sinkNonces : List Nat), Accepted d → ExtractionFaithful d r actual → BrokerProtocolRefinement d R cap t sinkNonces → sinkNonces.length < cap
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_16

namespace ReviewProof_g0_16
open PL_g0_16
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro h
 have bad := h clean Witnesses.receiverNode Witnesses.R 1 Witnesses.s5 clean.edges [7] clean_accepted Witnesses.extracted Witnesses.refined
 change (1 : Nat) < 1 at bad
 omega
 theorem witness : Witness := clean_accepted

end ReviewProof_g0_16
#print axioms ReviewProof_g0_16.claim
#print axioms ReviewProof_g0_16.witness
