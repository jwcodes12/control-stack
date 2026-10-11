import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_12
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (a : Node) (target : Nat), Accepted d → a ∈ d.nodes → a.agent = true → target ≠ a.id → ¬ AvoidedPath d a.id target
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_12

namespace ReviewProof_g0_12
open PL_g0_12
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 let d : IR := {clean with edges := ⟨0,6,false,false,false⟩ :: clean.edges}
 have accepted : Accepted d := by decide
 have path : AvoidedPath d 0 6 := .step ⟨0,6,false,false,false⟩ (by decide) (by decide) (by decide) .refl
 intro h
 exact h d Witnesses.agentA 6 accepted (by decide) rfl (by decide) path
 theorem witness : Witness := clean_accepted

end ReviewProof_g0_12
#print axioms ReviewProof_g0_12.claim
#print axioms ReviewProof_g0_12.witness
