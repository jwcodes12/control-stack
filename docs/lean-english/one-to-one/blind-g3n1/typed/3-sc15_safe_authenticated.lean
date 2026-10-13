import ControlStack.Scenarios.AuthInstancesB

namespace ControlStack.AuthInstances

def Back_sc15_safe_authenticated : Prop :=
  ∀ (E : SC15.Env) (U : List ℕ) (ops : List (ℕ × SC15.Op)),
    (∀ c ∈ U, c ∉ E.reviewers ∧ c ∉ E.security) →
    let s := AuthenticatedLog.authRun (SC15.step E SC15.full) claim15 SC15.init ops
    (∀ c ∈ s.merged, SC15.MergeOk E s c) ∧
    (∀ r ∈ s.reviews,
      (r.reviewer, SC15.Op.review r.reviewer r.id r.sec) ∈ ops ∧
      r.reviewer ∉ U ∧ SC15.roleOk E r.sec r.reviewer = true)

end ControlStack.AuthInstances
