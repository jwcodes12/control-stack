namespace ControlStack.AuthInstances

-- U is the adversary's issuer set, represented by a predicate on principal ids.
def Back_sc19_safe_authenticated : Prop :=
  ∀ (E : ControlStack.SC19.Env) (U : ℕ → Prop)
      (ops : List (ℕ × ControlStack.SC19.Op)),
    (∀ c : ℕ, U c → c ∉ E.approvers) →
    (∀ c : ℕ, U c → c ∉ E.verifiers) →
    let s := ControlStack.AuthenticatedLog.authRun
      (ControlStack.SC19.step E ControlStack.SC19.full)
      claim19 ControlStack.SC19.init ops
    ControlStack.SC19.Good E s ∧
    (∀ a ∈ s.approvals,
      (a.2.1, ControlStack.SC19.Op.approve a.2.1 a.1) ∈ ops ∧
      a.2.1 ∈ E.approvers ∧ ¬ U a.2.1) ∧
    (∀ i ∈ s.verified,
      ∃ c : ℕ,
        (c, ControlStack.SC19.Op.verify c i) ∈ ops ∧
        c ∈ E.verifiers ∧ ¬ U c)

end ControlStack.AuthInstances
