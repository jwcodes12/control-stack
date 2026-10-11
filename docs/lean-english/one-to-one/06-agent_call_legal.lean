import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_06
open ControlStack ControlStack.Deployment
def Back (d : IR) (r a : Node) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) : Prop := a.uid ≠ r.uid
def Orig (d : IR) (r a : Node) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) : Prop := SC26.legal (roles d r.uid approvers admins) (.bankCall a.uid k tx)
def Claim : Prop := ∀ (d : IR) (r a : Node) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx), (Back d r a approvers admins k tx ↔ Orig d r a approvers admins k tx)
def Witness : Prop := Accepted clean
end PL_g0_06

namespace ReviewProof_g0_06
open PL_g0_06
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d r a approvers admins k tx
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d : IR) (h : Accepted d) (r a : Node) (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes) (agent : a.agent = true) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) : Orig d r a approvers admins k tx := agent_call_legal d h r a hr rid ha agent approvers admins k tx

end ReviewProof_g0_06
#print axioms ReviewProof_g0_06.claim
#print axioms ReviewProof_g0_06.witness
