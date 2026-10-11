import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_05
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (r : Node), Accepted d → r ∈ d.nodes → r.id = d.receiver → ∀ a ∈ d.nodes, a.uid ≠ r.uid
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_05

namespace ReviewProof_g0_05
open PL_g0_05
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro h
 have bad := h clean Witnesses.receiverNode clean_accepted (by decide) rfl Witnesses.receiverNode (by decide)
 exact bad rfl
 theorem witness : Witness := clean_accepted

end ReviewProof_g0_05
#print axioms ReviewProof_g0_05.claim
#print axioms ReviewProof_g0_05.witness
