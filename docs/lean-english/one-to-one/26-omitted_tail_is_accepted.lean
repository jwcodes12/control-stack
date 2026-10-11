import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_26
open ControlStack ControlStack.Deployment
def Back  : Prop := CheckedTrace.verified TranscriptReplay.table.step 0 (TranscriptReplay.receipts.take 9) = true
def Orig  : Prop := CheckedTrace.verified TranscriptReplay.table.step 0 TranscriptReplay.withoutLastRelease = true
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_26

namespace ReviewProof_g0_26
open PL_g0_26
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract : Orig := TranscriptReplay.omitted_tail_is_accepted

end ReviewProof_g0_26
#print axioms ReviewProof_g0_26.claim
#print axioms ReviewProof_g0_26.witness
