import ControlStack.Scenarios.SC16Disjoint

namespace ControlStack.SC16Disjoint

open ControlStack.SC16

def Back_sc16_safe_disjoint : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
    (∀ c ∈ R.reviewers, c ∉ R.agents) →
    (∀ c ∈ R.approvers, c ∉ R.agents) →
    let s := run R h full init ops
    let contents := s.deployed.map Dep.content ++ s.reviews.map Review.content
    (∀ (x y : ℕ), x ∈ contents → y ∈ contents → h x = h y → x = y) →
    ∀ e ∈ s.deployed,
      (∃ rv ∈ s.reviews,
        rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
        rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
      (∃ ap ∈ s.approvals,
        ap.n = e.n ∧ ap.target = e.target ∧
        ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)

end ControlStack.SC16Disjoint
