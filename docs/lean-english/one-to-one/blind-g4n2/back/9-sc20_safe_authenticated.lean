namespace ControlStack.AuthInstances

-- U is the adversary's issuer set, represented by a predicate on principal ids.
def Back_sc20_safe_authenticated : Prop :=
  ∀ (E : ControlStack.SC20.Env) (U : ℕ → Prop)
      (ops : List (ℕ × ControlStack.SC20.Op)),
    (∀ c : ℕ, U c → c ∉ E.reviewers) →
    let s := ControlStack.AuthenticatedLog.authRun
      (ControlStack.SC20.step E ControlStack.SC20.full)
      claim20 ControlStack.SC20.init ops
    ControlStack.SC20.Good E s ∧
    (∀ p ∈ s.promoted,
      (p.2.1, ControlStack.SC20.Op.promote p.2.1 p.1) ∈ ops ∧
      p.2.1 ∈ E.reviewers ∧ ¬ U p.2.1)

end ControlStack.AuthInstances
