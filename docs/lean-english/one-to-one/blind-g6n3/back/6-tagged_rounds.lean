import ControlStack.Scenarios.SC26LossyHalt

namespace ControlStack.SC26LossyHalt

open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26LossyLiveness

def Back_tagged_rounds : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)),
    (∀ o ∈ ops₀, legalL R o) →
    let start := runT R cap tinit ops₀
    (∀ o ∈ (rounds.map roundOps).flatten, legalL R o) →
    (∃ (before : List (List LOp × List LOp))
        (r : List LOp × List LOp) (after : List (List LOp × List LOp)),
      rounds = before ++ r :: after ∧
        DeliversT R cap k (runT R cap start (before.map roundOps).flatten) r) →
    let final := runT R cap start (rounds.map roundOps).flatten
    k ∈ final.c.bank.map Prod.fst ∧
      ∀ (continuation : List LOp),
        (∀ o ∈ continuation, legalL R o) →
        ((runT R cap final continuation).c.bank.map Prod.fst).count k = 1

end ControlStack.SC26LossyHalt
