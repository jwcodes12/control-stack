import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_13
open ControlStack ControlStack.Deployment
def Back (d : IR) (a : Node) : Prop := ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database
def Orig (d : IR) (a : Node) : Prop := ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database
def Claim : Prop := ∀ (d : IR) (a : Node), (Back d a ↔ Orig d a)
def Witness : Prop := Accepted clean
end PL_g0_13

namespace ReviewProof_g0_13
open PL_g0_13
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d a
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d larger : IR) (subset : ∀ e ∈ d.edges, e ∈ larger.edges) (nodes : d.nodes = larger.nodes) (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver) (sink : d.sink = larger.sink) (database : d.database = larger.database) (accepted : Accepted larger) (a : Node) (member : a ∈ d.nodes) (agent : a.agent = true) : Orig d a := accepted_path_safety_monotone d larger subset nodes broker receiver sink database accepted a member agent

end ReviewProof_g0_13
#print axioms ReviewProof_g0_13.claim
#print axioms ReviewProof_g0_13.witness
