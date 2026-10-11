import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace PL_g0_11
open ControlStack ControlStack.Deployment
def Back (d : IR) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (actual : List Edge) (sinkEffects : List (Nat × SC26.Tx)) : Prop := (∀ e ∈ actual, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧ (∀ e ∈ sinkEffects, ∃ req, SC26.reqOf (SC26.run R cap SC26.full SC26.init ops) e.1 = some req ∧ req.tx = e.2 ∧ e.1 ∈ (SC26.run R cap SC26.full SC26.init ops).reserved ∧ SC26.Approved R (SC26.run R cap SC26.full SC26.init ops) e.1 req) ∧ (sinkEffects.map Prod.fst).Nodup ∧ (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧ sinkEffects.length ≤ cap
def Orig (d : IR) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (actual : List Edge) (sinkEffects : List (Nat × SC26.Tx)) : Prop := (∀ e ∈ actual, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧ (∀ e ∈ sinkEffects, ∃ req, SC26.reqOf (SC26.run R cap SC26.full SC26.init ops) e.1 = some req ∧ req.tx = e.2 ∧ e.1 ∈ (SC26.run R cap SC26.full SC26.init ops).reserved ∧ SC26.Approved R (SC26.run R cap SC26.full SC26.init ops) e.1 req) ∧ (sinkEffects.map Prod.fst).Nodup ∧ (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧ sinkEffects.length ≤ cap
def Claim : Prop := ∀ (d : IR) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (actual : List Edge) (sinkEffects : List (Nat × SC26.Tx)), (Back d R cap ops actual sinkEffects ↔ Orig d R cap ops actual sinkEffects)
def Witness : Prop := Accepted clean
end PL_g0_11

namespace ReviewProof_g0_11
open PL_g0_11
open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d R cap ops actual sinkEffects
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d : IR) (r : Node) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (actual : List Edge) (sinkEffects : List (Nat × SC26.Tx)) (h : Accepted d) (ext : ExtractionFaithful d r actual) (ref : ProtocolRefinement d r R cap ops sinkEffects) : Orig d R cap ops actual sinkEffects := deployment_safe d r R cap ops actual sinkEffects h ext ref

end ReviewProof_g0_11
#print axioms ReviewProof_g0_11.claim
#print axioms ReviewProof_g0_11.witness
