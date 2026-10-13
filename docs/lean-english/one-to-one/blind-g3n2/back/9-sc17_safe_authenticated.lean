import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.AuthInstances

open ControlStack.AuthenticatedLog

-- U is the adversary set. Provenance is membership in the issuer-labelled
-- input trace; no timing or competence property is added.
def Back_sc17_safe_authenticated : Prop :=
  ∀ (E : SC17.Env) (U : Set ℕ) (g0 : List SC17.G)
    (ops : List (ℕ × SC17.Op)),
    (∀ c ∈ U, c ∉ E.reviewers) →
      let s := authRun (SC17.step E SC17.full) claim17 (SC17.init g0) ops
      SC17.Good E s ∧
      (∀ a ∈ s.approvals,
        (a.reviewer, SC17.Op.approve a.reviewer a.id) ∈ ops ∧
        a.reviewer ∈ E.reviewers ∧ a.reviewer ∉ U) ∧
      (∀ p ∈ s.props,
        (p.author, SC17.Op.propose p.author p.id p.diff) ∈ ops ∨
        (p.author, SC17.Op.amend p.author p.id p.diff) ∈ ops)

end ControlStack.AuthInstances
