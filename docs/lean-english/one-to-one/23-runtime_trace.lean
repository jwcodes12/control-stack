import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_23
open ControlStack ControlStack.Deployment
def Back  : Prop := TrustedBroker.Trace TranscriptReplay.R (TrustedBroker.initial 2) TranscriptReplay.s10
def Orig  : Prop := TrustedBroker.Trace TranscriptReplay.R (TrustedBroker.initial 2) TranscriptReplay.s10
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_23

namespace ReviewProof_g0_23
open PL_g0_23
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract : Orig := TranscriptReplay.runtime_trace

end ReviewProof_g0_23
#print axioms ReviewProof_g0_23.claim
#print axioms ReviewProof_g0_23.witness
