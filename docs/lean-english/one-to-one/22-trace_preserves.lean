import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_22
open ControlStack ControlStack.Deployment
def Back (t : TrustedBroker.State) : Prop := t.spent ≤ t.cap ∧ t.releases ≤ t.spent ∧ t.consumed.Nodup ∧ ∀ k l, t.leases k = some l → l.used ≤ l.budget
def Orig (t : TrustedBroker.State) : Prop := TrustedBroker.Safe t
def Claim : Prop := ∀ (t : TrustedBroker.State), (Back t ↔ Orig t)
def Witness : Prop := Accepted clean
end PL_g0_22

namespace ReviewProof_g0_22
open PL_g0_22
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro t
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (s t : TrustedBroker.State) (safe : TrustedBroker.Safe s) (trace : TrustedBroker.Trace R s t) : Orig t := TrustedBroker.trace_preserves R s t safe trace

end ReviewProof_g0_22
#print axioms ReviewProof_g0_22.claim
#print axioms ReviewProof_g0_22.witness
