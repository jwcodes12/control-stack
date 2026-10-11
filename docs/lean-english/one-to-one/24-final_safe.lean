import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_24
open ControlStack ControlStack.Deployment
def Back  : Prop := TranscriptReplay.s10.spent ≤ TranscriptReplay.s10.cap ∧ TranscriptReplay.s10.releases ≤ TranscriptReplay.s10.spent ∧ TranscriptReplay.s10.consumed.Nodup ∧ ∀ k l, TranscriptReplay.s10.leases k = some l → l.used ≤ l.budget
def Orig  : Prop := TrustedBroker.Safe TranscriptReplay.s10
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_24

namespace ReviewProof_g0_24
open PL_g0_24
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract : Orig := TranscriptReplay.final_safe

end ReviewProof_g0_24
#print axioms ReviewProof_g0_24.claim
#print axioms ReviewProof_g0_24.witness
