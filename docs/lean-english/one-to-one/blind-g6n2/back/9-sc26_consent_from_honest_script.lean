namespace ControlStack.AuthenticatedAdv

open ControlStack.SC26 ControlStack.SC26Authenticated
open ControlStack.Authenticated ControlStack.Gate

def Back_sc26_consent_from_honest_script : Prop :=
  ∀ (R : Roles) (cap : ℕ) (U : List ℕ)
    (hon ops : List (ℕ × Op)),
    AdvTrace U hon ops →
    (∀ a ∈ R.approvers, a ∉ U) →
    R.gate ∉ U →
    (∀ io ∈ hon,
      match io.2 with
      | .bankCall _ _ _ => io.1 ≠ R.gate
      | _ => True) →
    let s := (authed (raw R cap) claim).run init ops
    Good R cap s ∧
    (∀ e ∈ s.bank,
      ∃ a : ℕ,
        a ∈ R.approvers ∧
        (a, Op.approve a e.1 e.2) ∈ hon)

end ControlStack.AuthenticatedAdv
