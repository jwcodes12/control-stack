import ControlStack.Deployment.NamedContracts
import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.R2Contracts

/-!
Guard deletion experiments. A countermodel here concerns the *model* and
the stated property, not the live broker. The remaining guard conjunction is
explicitly checked for each concrete broker witness. For the two graph
conclusions, we prove the stronger fact that the *whole* sibling group of
guards can be omitted when NoBypass or BaseAccepted respectively remains.
No non-standard axioms are introduced.
-/
namespace ControlStack.Deployment.GuardNecessity
open ControlStack
open ControlStack.TrustedBroker
open ControlStack.Deployment
open ControlStack.Deployment.Witnesses

/-- Removing precisely one numbered condition (0..20), retaining the other 20. -/
def AllowedExcept (omit : Nat) (R : TrustedBroker.Roles) (s : TrustedBroker.State)
    (now : Nat) (r : TrustedBroker.Request) (a : TrustedBroker.Approval)
    (l : TrustedBroker.Lease) : Prop :=
  (omit = 0 ∨ s.halted = false) ∧
  (omit = 1 ∨ R.agent r.uid) ∧
  (omit = 2 ∨ s.approvals r.nonce = some a) ∧
  (omit = 3 ∨ a.used = false) ∧
  (omit = 4 ∨ a.digest = r.digest) ∧
  (omit = 5 ∨ a.destination = r.destination) ∧
  (omit = 6 ∨ a.agent = r.uid) ∧
  (omit = 7 ∨ a.lease = r.lease) ∧
  (omit = 8 ∨ R.approver a.signer) ∧
  (omit = 9 ∨ now < a.expires) ∧
  (omit = 10 ∨ s.leases r.lease = some l) ∧
  (omit = 11 ∨ l.agent = r.uid) ∧
  (omit = 12 ∨ l.revoked = false) ∧
  (omit = 13 ∨ now < l.expires) ∧
  (omit = 14 ∨ 0 < r.cost) ∧
  (omit = 15 ∨ l.used + r.cost ≤ l.budget) ∧
  (omit = 16 ∨ s.spent + r.cost ≤ s.cap) ∧
  (omit = 17 ∨ s.artifacts r.digest = true) ∧
  (omit = 18 ∨ s.intact r.digest = true) ∧
  (omit = 19 ∨ ∃ reviewer, s.reviews r.digest = some reviewer) ∧
  (omit = 20 ∨ r.nonce ∉ s.consumed)

private theorem s4_safe : TrustedBroker.Safe Witnesses.s4 :=
  TrustedBroker.trace_preserves Witnesses.R _ _
    (TrustedBroker.initial_safe 1)
    (.cons Witnesses.staged
      (.cons Witnesses.reviewed
        (.cons Witnesses.issued (.cons Witnesses.approved (.nil _)))))

private def zeroCost : TrustedBroker.Request := {Witnesses.request with cost := 0}
private def highCost : TrustedBroker.Request := {Witnesses.request with cost := 2}
private def stopped : TrustedBroker.State := {Witnesses.s4 with halted := true}
private def localOver : TrustedBroker.State := {Witnesses.s4 with cap := 3}
private def largerLease : TrustedBroker.Lease := {Witnesses.lease with budget := 2}
private def globalOver : TrustedBroker.State :=
  {Witnesses.s4 with leases := TrustedBroker.put Witnesses.s4.leases 9 (some largerLease)}
private def duplicate : TrustedBroker.State := {Witnesses.s4 with consumed := [7]}

set_option maxRecDepth 2000 in
theorem no_halt_guard_other_twenty :
    AllowedExcept 0 Witnesses.R stopped 0 Witnesses.request Witnesses.approval Witnesses.lease := by
  simp [AllowedExcept, stopped, Witnesses.R, Witnesses.s4, Witnesses.s3,
    Witnesses.s2, Witnesses.s1, Witnesses.s0, Witnesses.lease,
    Witnesses.approval, Witnesses.request, TrustedBroker.initial, TrustedBroker.put]
theorem no_halt_guard_breaks_absorption :
    stopped.halted = true ∧
      (TrustedBroker.committed stopped Witnesses.request Witnesses.approval Witnesses.lease).releases
        ≠ stopped.releases := by decide

set_option maxRecDepth 2000 in
theorem no_positive_cost_guard_other_twenty :
    AllowedExcept 14 Witnesses.R Witnesses.s4 0 zeroCost Witnesses.approval Witnesses.lease := by
  simp [AllowedExcept, zeroCost, Witnesses.R, Witnesses.s4, Witnesses.s3,
    Witnesses.s2, Witnesses.s1, Witnesses.s0, Witnesses.lease,
    Witnesses.approval, Witnesses.request, TrustedBroker.initial, TrustedBroker.put]
theorem no_positive_cost_guard_breaks_safe :
    TrustedBroker.Safe Witnesses.s4 ∧
      ¬ TrustedBroker.Safe (TrustedBroker.committed Witnesses.s4 zeroCost
        Witnesses.approval Witnesses.lease) := by
  refine ⟨s4_safe, ?_⟩
  intro h
  have bad : ¬ (TrustedBroker.committed Witnesses.s4 zeroCost
    Witnesses.approval Witnesses.lease).releases ≤
    (TrustedBroker.committed Witnesses.s4 zeroCost
    Witnesses.approval Witnesses.lease).spent := by decide
  exact bad h.2.1

set_option maxRecDepth 2000 in
theorem no_local_budget_guard_other_twenty :
    AllowedExcept 15 Witnesses.R localOver 0 highCost Witnesses.approval Witnesses.lease := by
  simp [AllowedExcept, localOver, highCost, Witnesses.R, Witnesses.s4,
    Witnesses.s3, Witnesses.s2, Witnesses.s1, Witnesses.s0,
    Witnesses.lease, Witnesses.approval, Witnesses.request,
    TrustedBroker.initial, TrustedBroker.put]
theorem no_local_budget_guard_breaks_safe :
    ¬ TrustedBroker.Safe (TrustedBroker.committed localOver highCost
      Witnesses.approval Witnesses.lease) := by
  intro h
  have bound := h.2.2.2 9 {Witnesses.lease with used := 2} (by decide)
  have bad : ¬ ({Witnesses.lease with used := 2} : TrustedBroker.Lease).used ≤
      ({Witnesses.lease with used := 2} : TrustedBroker.Lease).budget := by decide
  exact bad bound

set_option maxRecDepth 2000 in
theorem no_joint_budget_guard_other_twenty :
    AllowedExcept 16 Witnesses.R globalOver 0 highCost Witnesses.approval largerLease := by
  simp [AllowedExcept, globalOver, largerLease, highCost, Witnesses.R,
    Witnesses.s4, Witnesses.s3, Witnesses.s2, Witnesses.s1, Witnesses.s0,
    Witnesses.lease, Witnesses.approval, Witnesses.request,
    TrustedBroker.initial, TrustedBroker.put]
theorem no_joint_budget_guard_breaks_safe :
    ¬ TrustedBroker.Safe (TrustedBroker.committed globalOver highCost
      Witnesses.approval largerLease) := by
  intro h
  have bad : ¬ (TrustedBroker.committed globalOver highCost
      Witnesses.approval largerLease).spent ≤
      (TrustedBroker.committed globalOver highCost
      Witnesses.approval largerLease).cap := by decide
  exact bad h.1

set_option maxRecDepth 2000 in
theorem no_nonce_guard_other_twenty :
    AllowedExcept 20 Witnesses.R duplicate 0 Witnesses.request Witnesses.approval Witnesses.lease := by
  simp [AllowedExcept, duplicate, Witnesses.R, Witnesses.s4, Witnesses.s3,
    Witnesses.s2, Witnesses.s1, Witnesses.s0, Witnesses.lease,
    Witnesses.approval, Witnesses.request, TrustedBroker.initial, TrustedBroker.put]
theorem no_nonce_guard_breaks_safe :
    ¬ TrustedBroker.Safe (TrustedBroker.committed duplicate
      Witnesses.request Witnesses.approval Witnesses.lease) := by
  intro h
  have bad : ¬ (TrustedBroker.committed duplicate
      Witnesses.request Witnesses.approval Witnesses.lease).consumed.Nodup := by decide
  exact bad h.2.2.1

/-- Neither BaseAccepted nor WritersChecked is needed for the path theorem,
if NoBypass is kept as an independent hypothesis. -/
theorem avoided_paths_from_nobypass (d : IR) (h : NoBypass d)
    (a : Node) (ha : a ∈ d.nodes) (agent : a.agent = true) :
    ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database := by
  obtain ⟨initial, sink, database, closed⟩ := h a ha agent
  exact ⟨fun p => sink (path_in_closed d a.id d.sink _ initial closed p),
    fun p => database (path_in_closed d a.id d.database _ initial closed p)⟩

/-- Sink-authority exclusivity needs no WritersChecked field when BaseAccepted holds. -/
theorem sink_from_base_without_writers (d : IR) (h : BaseAccepted d)
    (e : Edge) (member : e ∈ d.edges) (authority : e.authority = true)
    (sink : e.target = d.sink) : e.source = d.receiver :=
  h.2.1 e member authority sink

/-- Conversely the first WritersChecked field covers exclusivity without BaseAccepted. -/
theorem sink_from_writers_without_base (d : IR) (h : WritersChecked d)
    (e : Edge) (member : e ∈ d.edges) (_authority : e.authority = true)
    (sink : e.target = d.sink) : e.source = d.receiver :=
  (h.1 e member sink).1

end ControlStack.Deployment.GuardNecessity

#print axioms ControlStack.Deployment.GuardNecessity.no_positive_cost_guard_breaks_safe
#print axioms ControlStack.Deployment.GuardNecessity.no_local_budget_guard_breaks_safe
#print axioms ControlStack.Deployment.GuardNecessity.no_joint_budget_guard_breaks_safe
#print axioms ControlStack.Deployment.GuardNecessity.no_nonce_guard_breaks_safe
#print axioms ControlStack.Deployment.GuardNecessity.avoided_paths_from_nobypass
#print axioms ControlStack.Deployment.GuardNecessity.sink_from_base_without_writers
