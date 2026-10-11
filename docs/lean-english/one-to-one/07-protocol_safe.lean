import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_07
open ControlStack ControlStack.Deployment
def Back (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop := let s := SC26.run R cap SC26.full SC26.init ops; (∀ e ∈ s.bank, ∃ req, SC26.reqOf s e.1 = some req ∧ req.tx = e.2 ∧ e.1 ∈ s.reserved ∧ SC26.Approved R s e.1 req) ∧ (s.bank.map Prod.fst).Nodup ∧ (s.bank.map (fun e => e.2.amount)).sum ≤ cap
def Orig (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop := SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)
def Claim : Prop := ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op), (Back R cap ops ↔ Orig R cap ops)
def Witness : Prop := Accepted clean
end PL_g0_07

namespace ReviewProof_g0_07
open PL_g0_07
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R cap ops
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (h : ∀ o ∈ ops, SC26.legal R o) : Orig R cap ops := protocol_safe R cap ops h

end ReviewProof_g0_07
#print axioms ReviewProof_g0_07.claim
#print axioms ReviewProof_g0_07.witness
