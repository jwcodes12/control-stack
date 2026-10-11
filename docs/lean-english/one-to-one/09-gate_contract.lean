import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_09
open ControlStack ControlStack.Deployment
def Back (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Prop := (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧ (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧ ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops), (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e
def Orig (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Prop := (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧ (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧ ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops), (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e
def Claim : Prop := ∀ (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}), (Back R cap ops ↔ Orig R cap ops)
def Witness : Prop := Accepted clean
end PL_g0_09

namespace ReviewProof_g0_09
open PL_g0_09
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R cap ops
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Orig R cap ops := gate_contract R cap ops

end ReviewProof_g0_09
#print axioms ReviewProof_g0_09.claim
#print axioms ReviewProof_g0_09.witness
