import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_14
open ControlStack ControlStack.Deployment
def Back (larger : IR) (start target : Nat) : Prop := AvoidedPath larger start target
def Orig (larger : IR) (start target : Nat) : Prop := AvoidedPath larger start target
def Claim : Prop := ∀ (larger : IR) (start target : Nat), (Back larger start target ↔ Orig larger start target)
def Witness : Prop := Accepted clean
end PL_g0_14

namespace PLProof_g0_14_50b14d383650
open PL_g0_14
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro larger start target
 rfl
theorem witness : Witness := clean_accepted

end PLProof_g0_14_50b14d383650
theorem gate_50b14d383650 : PL_g0_14.Claim := PLProof_g0_14_50b14d383650.claim
#print axioms gate_50b14d383650
