import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_19
open ControlStack ControlStack.Deployment
def Back (t : TrustedBroker.State) : Prop := ∀ nonce, nonce ∈ t.consumed ↔ ∃ a, t.approvals nonce = some a ∧ a.used = true
def Orig (t : TrustedBroker.State) : Prop := TrustedBroker.Coherent t
def Claim : Prop := ∀ (t : TrustedBroker.State), (Back t ↔ Orig t)
def Witness : Prop := Accepted clean
end PL_g0_19

namespace ReviewProof_g0_19
open PL_g0_19
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro t
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (s t : TrustedBroker.State) (coherent : TrustedBroker.Coherent s) (step : TrustedBroker.Step R s t) : Orig t := TrustedBroker.transaction_coherent R s t coherent step

end ReviewProof_g0_19
#print axioms ReviewProof_g0_19.claim
#print axioms ReviewProof_g0_19.witness
