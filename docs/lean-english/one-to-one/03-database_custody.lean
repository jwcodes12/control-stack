import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_03
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.database → e.source = d.receiver
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_03

namespace ReviewProof_g0_03
open PL_g0_03
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro h
 have bad := h clean ⟨2,5,true,false,true⟩ clean_accepted (by decide) rfl rfl
 change (2 : Nat) = 3 at bad
 omega
 theorem witness : Witness := clean_accepted

end ReviewProof_g0_03
#print axioms ReviewProof_g0_03.claim
#print axioms ReviewProof_g0_03.witness
