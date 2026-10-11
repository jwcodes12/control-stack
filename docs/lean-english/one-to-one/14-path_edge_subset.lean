import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_14
open ControlStack ControlStack.Deployment
def Back (larger : IR) (start target : Nat) : Prop := AvoidedPath larger start target
def Orig (larger : IR) (start target : Nat) : Prop := AvoidedPath larger start target
def Claim : Prop := ∀ (larger : IR) (start target : Nat), (Back larger start target ↔ Orig larger start target)
def Witness : Prop := Accepted clean
end PL_g0_14

namespace ReviewProof_g0_14
open PL_g0_14
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro larger start target
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d larger : IR) (subset : ∀ e ∈ d.edges, e ∈ larger.edges) (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver) (start target : Nat) (path : AvoidedPath d start target) : Orig larger start target := path_edge_subset d larger subset broker receiver start target path

end ReviewProof_g0_14
#print axioms ReviewProof_g0_14.claim
#print axioms ReviewProof_g0_14.witness
