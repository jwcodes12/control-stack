import ControlStack.Scenarios.SC26LossyLiveness

namespace ControlStack.SC26LossyLiveness

open ControlStack.SC26 ControlStack.SC26Refinement

def Back_lossy_rounds : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)),
    (∀ o ∈ ops₀, legalL R o) →
    let start := runL R cap true cinit ops₀
    (∃ d ∈ start.delivery, d.id = k) →
    (∀ o ∈ (rounds.map roundOps).flatten, legalL R o) →
    (∃ r ∈ rounds, Delivers k r) →
    let final := runL R cap true start (rounds.map roundOps).flatten
    final.halted = false →
    k ∈ final.bank.map Prod.fst ∧
      ∀ (continuation : List LOp),
        (∀ o ∈ continuation, legalL R o) →
        ((runL R cap true final continuation).bank.map Prod.fst).count k = 1

end ControlStack.SC26LossyLiveness
