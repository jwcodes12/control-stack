import ControlStack.Scenarios.SC16Refinement

namespace ControlStack.SC16Refinement

-- Injectivity is restricted to deployed contents and reviewed contents
-- in the abstracted final state, rather than to all natural numbers.
def Back_concrete_reviewed_content : Prop :=
  ∀ (R : SC16.Roles) (h : ℕ → ℕ) (ops : List COp),
    let s := α (runC R h false cinit ops)
    let contents := s.deployed.map SC16.Dep.content ++
      s.reviews.map SC16.Review.content
    (∀ x ∈ contents, ∀ y ∈ contents, h x = h y → x = y) →
      ∀ e ∈ s.deployed,
        ∃ rv ∈ s.reviews,
          e.content = rv.content ∧
          rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager

end ControlStack.SC16Refinement
