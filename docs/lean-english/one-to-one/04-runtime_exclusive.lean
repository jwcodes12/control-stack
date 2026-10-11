import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_04
open ControlStack ControlStack.Deployment
def Back (d : IR) (actual : List Edge) (e : Edge) : Prop := e.source = d.receiver
def Orig (d : IR) (actual : List Edge) (e : Edge) : Prop := e.source = d.receiver
def Claim : Prop := ∀ (d : IR) (actual : List Edge) (e : Edge), (Back d actual e ↔ Orig d actual e)
def Witness : Prop := Accepted clean
end PL_g0_04

namespace ReviewProof_g0_04
open PL_g0_04
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d actual e
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d : IR) (actual : List Edge) (h : Accepted d) (faithful : Faithful d actual) (e : Edge) (member : e ∈ actual) (authority : e.authority = true) (sink : e.target = d.sink) : Orig d actual e := runtime_exclusive d actual h faithful e member authority sink

end ReviewProof_g0_04
#print axioms ReviewProof_g0_04.claim
#print axioms ReviewProof_g0_04.witness
