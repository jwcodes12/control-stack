import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

def Back_sc16_safe_authenticated : Prop :=
  ∀ (R : SC16.Roles) (h : ℕ → ℕ) (U : List ℕ)
    (ops : List (ℕ × SC16.Op)),
    (∀ c ∈ U, c ∉ R.reviewers ∧ c ∉ R.approvers) →
    let s := AuthenticatedLog.authRun (SC16.step R h SC16.full) claim16 SC16.init ops
    SC16.Good R h s ∧
    (∀ rv ∈ s.reviews,
      (rv.reviewer, SC16.Op.review rv.reviewer rv.d) ∈ ops ∧
      rv.reviewer ∉ U ∧ rv.reviewer ∈ R.reviewers) ∧
    (∀ ap ∈ s.approvals,
      (ap.approver, SC16.Op.approve ap.approver ap.n ap.d ap.target ap.slot) ∈ ops ∧
      ap.approver ∉ U ∧ ap.approver ∈ R.approvers)

end ControlStack.AuthInstances
