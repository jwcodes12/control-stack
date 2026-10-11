import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_15
open ControlStack ControlStack.Deployment
def Back  : Prop := sinkOnly.nodes = clean.nodes ∧ (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ (∃ e ∈ sinkOnly.edges, e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧ Accepted clean ∧ ¬ Accepted sinkOnly
def Orig  : Prop := sinkOnly.nodes = clean.nodes ∧ (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ (∃ e ∈ sinkOnly.edges, e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧ Accepted clean ∧ ¬ Accepted sinkOnly
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_15

namespace ReviewProof_g0_15
open PL_g0_15
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract : Orig := requested_monotonicity_counterexample

end ReviewProof_g0_15
#print axioms ReviewProof_g0_15.claim
#print axioms ReviewProof_g0_15.witness
