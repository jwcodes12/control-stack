import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_01
open ControlStack ControlStack.Deployment
def IdentityEnglish (d : IR) : Prop := ∀ a ∈ d.nodes, ∀ b ∈ d.nodes, a.id ≠ b.id → a.uid = b.uid → ((a.id = d.broker ∧ b.id = d.receiver) ∨ (a.id = d.receiver ∧ b.id = d.broker))
def Back (d : IR) : Prop := BaseAccepted d ∧ RoleChecked d ∧ IdentityEnglish d ∧ (∀ n ∈ d.nodes, n.runtimeMatch = true) ∧ WritersChecked d ∧ NoBypass d
def distinctBroker : IR := {clean with nodes := clean.nodes.map (fun n => if n.id = clean.broker then {n with uid := 23706} else n)}
def Claim : Prop := (∀ d, Accepted d → Back d) ∧ (Back distinctBroker ∧ ¬ Accepted distinctBroker)
def Witness : Prop := Accepted clean
end PL_g0_01

namespace ReviewProof_g0_01
open PL_g0_01
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 constructor
 · intro d h
   exact ⟨h.basic,h.roles,fun a ha b hb ne eq => (h.identities a ha b hb ne).mp eq,h.runtime,h.writers,h.bypass⟩
 · exact ⟨by unfold Back IdentityEnglish; decide,by decide⟩
theorem witness : Witness := clean_accepted

end ReviewProof_g0_01
#print axioms ReviewProof_g0_01.claim
#print axioms ReviewProof_g0_01.witness
