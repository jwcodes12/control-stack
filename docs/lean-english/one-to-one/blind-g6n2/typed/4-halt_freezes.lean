import ControlStack.Scenarios.SC26Transaction

namespace ControlStack.SC26

-- "Set of messages" is expressed by membership equivalence, without
-- asserting equality of the ordering or multiplicities in the net lists.
def Back_halt_freezes : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (ops : List Op),
    s.halted = true →
    (∀ o ∈ ops, legal R o) →
    let t := run R cap full s ops
    (∀ m : ℕ × Tx, m ∈ t.net ↔ m ∈ s.net) ∧
    (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.net)

end ControlStack.SC26
