import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_02
open ControlStack ControlStack.Deployment
def Back (d : IR) (e : Edge) : Prop := e.source = d.receiver ∨ e.source = d.broker
def Orig (d : IR) (e : Edge) : Prop := e.source = d.receiver
def Claim : Prop := (∀ d e, Orig d e → Back d e) ∧ (∃ d e, Back d e ∧ ¬ Orig d e)
def Witness : Prop := Accepted clean
end PL_g0_02

namespace ReviewProof_g0_02
open PL_g0_02
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 constructor
 · intro d e h
   exact Or.inl h
 · exact ⟨clean,⟨2,4,true,false,true⟩,Or.inr rfl,by unfold Orig; decide⟩
theorem witness : Witness := clean_accepted

theorem equivalent_on_accepted (d : IR) (e : Edge) (h : Accepted d) (member : e ∈ d.edges) (authority : e.authority = true) (sink : e.target = d.sink) : Back d e ↔ Orig d e := ⟨fun _ => exclusive_sink d h e member authority sink,Or.inl⟩

end ReviewProof_g0_02
#print axioms ReviewProof_g0_02.claim
#print axioms ReviewProof_g0_02.witness
