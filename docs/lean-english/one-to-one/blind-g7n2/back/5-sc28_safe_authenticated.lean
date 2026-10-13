import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

def Back_sc28_safe_authenticated : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (U : Set ℕ)
    (ops : List (ℕ × SC28.Op)),
    (∀ c ∈ admins, c ∉ U) →
    (∀ io ∈ ops, SC28.legal io.2) →
    let s := AuthenticatedLog.authRun
      (SC28.step admins G SC28.full) claim28 SC28.init ops
    SC28.Good G s ∧
      (∀ lease ∈ s.leases,
        ∃ c, c ∈ admins ∧ c ∉ U ∧
          (c, SC28.Op.issue c lease.1 lease.2) ∈ ops) ∧
      (∀ lid ∈ s.revoked,
        ∃ c, c ∈ admins ∧ c ∉ U ∧
          (c, SC28.Op.revoke c lid) ∈ ops)

end ControlStack.AuthInstances
