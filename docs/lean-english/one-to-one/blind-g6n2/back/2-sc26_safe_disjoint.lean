namespace ControlStack.SC26

def Back_sc26_safe_disjoint : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    (∀ a ∈ R.approvers, a ∉ R.agents) →
    (∀ o ∈ ops, legal R o) →
    let s := run R cap full init ops
    ∀ e ∈ s.bank,
      ∃ (r : Req) (a : ℕ),
        reqOf s e.1 = some r ∧
        r.tx = e.2 ∧
        (e.1, a, e.2) ∈ s.approvals ∧
        a ∈ R.approvers ∧
        a ∉ R.agents ∧
        a ≠ r.requester

end ControlStack.SC26
