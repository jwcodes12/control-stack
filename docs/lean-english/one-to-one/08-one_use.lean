import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_08
open ControlStack ControlStack.Deployment
def Back (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop := (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup
def Orig (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop := (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup
def Claim : Prop := ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op), (Back R cap ops ↔ Orig R cap ops)
def Witness : Prop := Accepted clean
end PL_g0_08

namespace ReviewProof_g0_08
open PL_g0_08
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R cap ops
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Orig R cap ops := one_use R cap ops

end ReviewProof_g0_08
#print axioms ReviewProof_g0_08.claim
#print axioms ReviewProof_g0_08.witness
