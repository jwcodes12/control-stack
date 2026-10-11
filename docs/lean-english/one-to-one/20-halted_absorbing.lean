import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_20
open ControlStack.Deployment
def Back (R : ControlStack.TrustedBroker.Roles) (s t : ControlStack.TrustedBroker.State) : Prop := t = s
 def Orig (s t : ControlStack.TrustedBroker.State) : Prop := t.halted = true ∧ t.releases = s.releases
 def Claim : Prop := ∀ (R : ControlStack.TrustedBroker.Roles) (s t : ControlStack.TrustedBroker.State), s.halted = true → ControlStack.TrustedBroker.Step R s t → (Back R s t ↔ Orig s t)
 def Witness : Prop := Accepted clean
end PL_g0_20

namespace ReviewProof_g0_20
open PL_g0_20
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R s t halted step
 have same : t = s := by
  cases step <;> first | rfl | simp_all [ControlStack.TrustedBroker.Allowed] | rw [← halted]
 constructor
 · intro h
   exact ControlStack.TrustedBroker.halted_absorbing R s t halted step
 · intro _
   exact same
 theorem witness : Witness := clean_accepted

end ReviewProof_g0_20
#print axioms ReviewProof_g0_20.claim
#print axioms ReviewProof_g0_20.witness
