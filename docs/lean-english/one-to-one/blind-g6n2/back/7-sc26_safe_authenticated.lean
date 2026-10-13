namespace ControlStack.SC26Authenticated

open ControlStack.SC26 ControlStack.Authenticated ControlStack.Gate

def Back_sc26_safe_authenticated : Prop :=
  ∀ (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)),
    (∀ a ∈ R.approvers, a ∉ U) →
    (∀ io ∈ ops,
      match io.2 with
      | .bankCall _ _ _ => io.1 ≠ R.gate
      | _ => True) →
    let s := (authed (raw R cap) claim).run init ops
    Good R cap s ∧
    (∀ e ∈ s.bank,
      ∃ a : ℕ,
        a ∈ R.approvers ∧
        a ∉ U ∧
        (a, Op.approve a e.1 e.2) ∈ ops)

end ControlStack.SC26Authenticated
