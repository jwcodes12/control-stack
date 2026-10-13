import ControlStack.Scenarios.SC16Deploy

namespace ControlStack.SC16

def Back_sc16_reviewed_content : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
    let s := run R h full init ops
    let contents := s.deployed.map Dep.content ++ s.reviews.map Review.content
    (∀ (x y : ℕ), x ∈ contents → y ∈ contents → h x = h y → x = y) →
    ∀ e ∈ s.deployed,
      ∃ rv ∈ s.reviews,
        rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager

end ControlStack.SC16
